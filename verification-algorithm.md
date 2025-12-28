# Algorithm for verifying a program using LLMs and a verifier (e.g., CBMC)

Overall idea:  The algorithm verifies a program by verifying one function at a
time, generally in reverse topological order.

A "proof state" is a pair of:

* a workstack of functions yet to be processed (in reverse topological order)
* the current specification of every function

A "step" is an attempt to verify the function on the top of the workstack.
A step converts one proof state into another.
The resulting proof state might have a smaller workstack (if verification
succeeded), or it might have a larger workstack (representing backtracking:
re-examination of a previously-considered function).

Each LLM call returns multiple possibilities or "samples".  (This avoids getting
stuck in one unproductive avenue.)  Therefore, each step actually yields a *set*
of proof states.  The implementation explores these possibilities in parallel (a
heuristic prunes or prioritizes the possibilities).

## Parameters

Two integers parameterize the algorithm:

* `num_llm_samples`: each call to `llm()` returns a list of this length.
  As a general rule, after each call to `llm()`, our algorithm heuristically
  prunes the returned list of samples to reduce the exploration space.
* `num_repair_iterations`: the number of times that the LLM tries to repair a
  specification, using feedback from running the verifier.

The implementation also contains:

* the model temperature, which cannot be set to 0 for sampling/generating candidates.

## Data structures

immutable class VerificationInput:

* function
* spec for function
* context: Context

Context (defined just below) represents specifications other relevant parts
(other than the method under verification).  Each context is a subset of a
ProofState, created by calling `current_context(fn, proofstate)`.  The program
does not directly manipulate contexts; they are an internal detail of caching.
They are used as keys for caching (rather than a ProofState) because they
contain only the relevant parts of a ProofState, which reduces the number of
possible keys and the likelihood of hitting in the cache.

immutable class Context:

* a spec for each of the function's callees.  Contains no specs for other functions in the program.
* a spec for each global variable that the function uses
* optionally, facts about how the function is called, such as what values are
  actually passed to it at call sites.  The algorithm might use these as
  preconditions, as opposed to the preconditions that an LLM would guess just
  by looking at the function's source code and comments.  (I admit this is a
  bit vague.)

immutable class VerificationResult:

* input: VerificationInput
* succeeded: boolean
* failure_messages: String | None

It doesn't make sense to say that a function specification in isolation is
verified or not, because the verification result depends on the full verifier
input, which includes the specifications of the callees and callers.

Global data structures:

* `verifier_outputs`:  Map[VerificationInput, VerificationResult].
  A cache for efficiency.  Is only added to, never removed from.
  This cache eliminates the need to pass VerificationResults through the program,
  since they can just be looked up.
* `llm_cache`: Map[LlmInput, List[LlmOutput]]: for efficiency.  Is only added to, never removed from.
  The input type (the key) is probably String.  Each value in the map is a list
  of strings, with length `num_llm_samples`.
  * Cache responses for testing + in cases where we make the same call to the LLM (given that it's
    the same LLM and not an "improved" model or the same call made some timeframe after the last
    call).
* `proofstates_worklist`:  set of ProofStates yet to be explored.
  Trying to add an element that has ever been previously added has no effect.
  (We could imagine making this a priority queue if we have a good heuristic for ordering.)

Each access to a global data structure must use locking; or we could store them
persistently, say using SQLite, which permits using multiprocessing rather than
multithreading and could save time across multiple runs.

class ProofState:

* specs: Map[Function, Specification]: the current specification (which may be a guess) for each function.
  * We can compute the verified/unverified/not-yet processed functions from a ProofState's `specs` map.
  * TODO: think about whether it's possible to obtain a list of assumed specs.
* workstack: Stack[WorkItem]
  A stack of functions that need to be (re)processed.
  Each hint is text provided to the LLM to guide it.  I don't have a data
  structure (beyond string) in mind for it yet.
  Example hints:
  * "Please weaken/strengthen the postcondition"
  * "This function is only ever called with non-null values",
  Invariant:  all the pairs with a non-empty `backtrack_hint` are above all the pairs with None.
  This is because every push onto the workstack has a non-None `backtrack_hint`.

Possible fields:

* verified_functions: a list of functions that have been verified.
* assumed_functions: a list of functions with unverified, but trusted, specifications.

immutable class SpecConversation:

* spec: Specification
* conversation: a conversation history with an LLM, that led to the given spec
* next_step_hint: Any hints for regenerating specifications, either for repair or for callees.

immutable class WorkItem:

* function: ParsecFunction
* next_step_hint: str

## Code

```python
def verify_program(program) -> List[Map[Fn, Spec]]:
  """
  The entry point: Verify all the functions in a program.
  Input: a program
  Output: a list of program specifications.  A program specification contains a specification for each function in the program
  """
  initial_workstack: Stack[(function, backtrack_hint)] = all functions in `program`, in reverse topological
                                                order (that is, children first), with empty backtrack_hint.
  initial_proofstate = ProofState(initial_workstack)
  global.proofstates_worklist.add(initial_proofstate)

  result = []
  while global.proofstates_worklist not empty and time() < TIMEOUT:
    proofstate = global.proofstates_worklist.remove_first()
    next_proofstates = step(proofstate)
    for next_proofstate in next_proofstates:
      if next_proofstate.workstack is empty:
        result.append(next_proofstate)
      else:
        global.proofstates_worklist.add(next_proofstate)
  return result

def step(proofstate: ProofState) -> List[ProofState]:
  """
  Given a ProofState, tries to verify the function at the top of the workstack.
  This is the key unit of parallelism.
  Input: a ProofState
  Output: a list of ProofStates resulting from the verification attempt.
    Let f be the top of the input's workstack.
    The output ProofState has a smaller workstack if f was successfully verified or if f's spec will be assumed.
    The output ProofState has a larger workstack (representing backtracking) if f was not successfully verified.
  """
  (fn, backtrack_hint) = proofstate.workstack.top();
  new_speccs: List[SpecConversation] = generate_and_repair_spec(fn, backtrack_hint)
  pruned_speccs = prune_heuristically(fn, candidate_speccs, proofstate)

  result = []
  for specc in pruned_speccs:
    next_proofstate = proofstate.clone()
    next_proofstate.specs[fn] = specc.spec
    last_llm_response = specc.conversation.last()
    if last_llm_response contains "backtrack":
      next_proofstate.workstack.push((last_llm_response.get_function(), last_llm_response))
    else:
      next_proofstate.workstack.pop() # pop off fn
    result.append(next_proofstate)
  return result

def generate_and_repair_spec(fn, backtrack_hint) -> List[SpecConversation]:
  """
  Generate a specification for a function.
  Input: a function and hints about how to specify it.  The hints are non-empty only when backtracking.
  Output: a list of potential specs for the function.  Some may verify and some may not verify.
  """
  generated_speccs = generate_speccs(fn, hint)
  pruned_specs = prune_heuristically(fn, generated_speccs)
  repaired_specs = [*repair_spec(fn, spec) for spec in pruned_specs]
  return repaired_specs

def prune_heuristically(fn, speccs: List[SpecConversation]) -> List[SpecConversation]:
  # Here is one example of a very simple heuristic for pruning:
  #  * If any spec verifies, return a list containing only the specs that verify.
  #  * Otherwise, return all the specs.

def generate_speccs(fn, hint) -> List[SpecConversation]:
  """
  An LLM guesses a specification.
  Input: a function and a hint.  The hint is plaintext.
  Output: a list of candidate specifications of length `num_llm_samples`.
  Implementation note: see LlmSpecificationGenerator.
  """
  llm_input = ("guess the specification for", fn, current_context(fn, proofstate), hint)
  specs = llm(llm_input) # call the LLM
  return [SpecConversation(spec, [llm_input]) for spec in specs]

def repair_spec(fn, specc, proofstate) -> List[SpecConversation]:
  """
  Given a specification, iteratively repair it.
  Input: a function and a specification.  The specification may or may not verify.
  Output: a list of repaired specifications.  Each may or may not verify.
  """
  # Implementation note: See `_get_repaired_specification` in `generate_speccs.py`.
  all_speccs = []  # Return every spec that was observed ...
  verified_speccs = []  # ... unless some were verified, in which case return only them.
  current_speccs = [specc]
  for i = 1 to num_repair_iterations:
    unverified_speccs = []  # Pairs of spec and conversation.
    for specc in current_speccs:
      if specc in all_speccs:
        # We have already seen this spec with this conversation, so don't re-process it.
        continue
      all_speccs.append(specc)
      vresult = call_verifier(fn, specc, proofstate) # e.g., CBMC
      if is_success(vresult):
        verified_speccs.append(specc)
      else:
        unverified_speccs.append(specc)
    current_speccs = []
    for (spec, conversation) in unverified_speccs:
      vresult = call_verifier(fn, spec, proofstate) # this VerificationResult is a verification failure
      # Update the conversation history and pass the full history to the LLM.
      new_conversation = conversation + [
        {
          "role": "user",
          "content": f"Verification error for {fn.name}: {error}. Either"
          + " (1) Repair the specification for {fn.name}.  Return the repaired specification for {fn.name}.  Or"
          + " (2) Retain the current specification for {fn.name} and choose a callee that needs a stronger specification in order to make {fn.name} verify."
          + " State the reasoning for why this is the case, and return the word 'backtrack', the callee function, and its stronger specification."
        }
      ]
      responses = llm(new_conversation, fn, spec) # TODO: Why pass in `fn` and `spec`? They appear in the conversation.
      # Each response forks a new conversation history
      current_speccs += [(response, new_conversation + [{"assistant": response}]) for response in responses]
  if verified_speccs:
    return verified_speccs:
  else:
    return all_speccs

def call_verifier(fn, specc, proofstate) -> VerificationResult:
  """
  Calls a verification tool such as CBMC.  Uses a cache to avoid recomputation.
  Input: the function, a specification, and context.
  Output: a verification result.
  """
  context = current_context(fn, proofstate)
  vinput = VerificationInput(fn, specc.spec, context)
  # look up in the cache, compute if necessary
  vresult = global.verifier_outputs[vinput]
  if vresult == None:
    vresult = CBMC(fn, spec, context)
    global.verifier_outputs[vinput] = vresult
  return vresult

def current_context(fn, proofstate) -> context:
  """
  Input: A function
  Output: the function's current verification context: the specs of callers and callees.
  """
  # Look up from proofstate's fields, such as `specs` or `verified_functions` and `assumed_functions`.

def llm(...):
  This is a function that calls the API we're using for LLMs.  It should use a cache.
```

Suppose that, after creating a VerificationInput, the system changes some
specification in the context.  Then the old VerificationInput is no longer
applicable.  A call to `call_verifier()` will create a new VerificationInput
and the verifier will be re-run.  (This is one reason that verification
results are not passed around in the algorithm, but are re-computed -- to
avoid the bookkeeping of figuring out what has to be updated.)

## Parallelization

Many for loops and list comprehensions (but not the for loop in `repair`) can be parallelized.

<!--
## OLD, NO LONGER RELEVANT

More about forking processes:

At each point that the LLM is invoked, the algorithm could call the LLM multiple times and pursue each of the possibilities (possibly in parallel).
Currently this is hard-coded in `generate_and_repair_spec()`, which is the client of `generate_speccs()` which calls the LLM to produce multiple results.
However, it is not done for other LLM calls in `repair_spec()` and `choose_next_step()`.

It would be better for the algorithm to apply sample-exploration more uniformly.

* One way is to hard-code the other LLM uses, just as `generate_speccs()` and its client `generate_and_repair_spec()` are.
* Another way is to modify the algorithm to fork multiple processes, like so:
  * Rewrite the algorithm to treat each LLM query call as returning exactly one value.  (This actually simplifies `generate_and_repair_spec()` and its client `verify_program()`.
  * Actually, each LLM query returns a list (which is different than the above rewriting).
    Fork N processes, one for for each element of the list.
    Each forked process has its own process state, which starts as a copy of the global variables and call stack.
  * Pruning processes:
    Whenever a process successfully completes a task (I'm not exactly sure what is the definition of "task" here), possibly prune all the siblings of this process that are still running, because they are no longer needed.
    This is similar to a process manager that prunes processes that have been superseded (that, is prune a process if some other process already solved the problem).
    A process manager would also prune processes that have run for too long.
-->

<!--
LocalWords:  workstack llm num VerificationInput VerificationResult boolean fn doesn SQLite multithreading WorkItem
LocalWords:  VerificationResults LlmInput LlmOutput proofstates ProofStates ps
LocalWords:  ProofState TODO f's vresult BacktrackInfo plaintext proofstate py
LocalWords:  LlmSpecificationGenerator recomputation vinput
-->
