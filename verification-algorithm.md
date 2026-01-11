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
  The algrithm pursues all these possibilities in parallel.
  As a general rule, after each call to `llm()`, our algorithm heuristically
  prunes the returned list of samples to reduce the exploration space.
  * The implementation calls the LLM for different purposes and therefore has multiple variables,
    one for each type of LLM query.
* `num_repair_iterations`: the number of times that the LLM tries to repair a
  specification, using feedback from running the verifier.

The implementation also contains:

* which model to use
* the model temperature, which cannot be set to 0 for sampling/generating candidates.

## Data structures

immutable class VerificationInput:

* function
* spec for function
* context: Context

Context (defined just below) represents specifications of other relevant parts (other than the
method under verification).  Each context is a subset of a ProofState, created by calling
`current_context(fn, proofstate)`.  The verification algorithm does not directly manipulate
contexts; they are an internal detail of caching.  They are used as keys for caching (rather than a
ProofState) because they contain only the relevant parts of a ProofState, which reduces the number
of possible keys and increases the likelihood of hitting in the cache.

immutable class Context:

* a spec for each of the function's callees.  Contains no specs for other functions in the program.
* a spec for each global variable that the function uses
* optionally, facts about how the function is called, such as what values are
  actually passed to it at call sites.  The algorithm might use these as
  preconditions, as opposed to the preconditions that an LLM would guess just
  by looking at the function's source code and comments.  (I admit this is a
  bit vague.)

immutable class VerificationResult:

* `input`: VerificationInput
* `succeeded`: boolean
* `failure_messages`: String | None

It doesn't make sense to say that a function specification in isolation is
verified or not, because the verification result depends on the full verifier
input, which includes the specifications of the callees.

Global data structures:

* `proofstates_worklist`:  set of ProofStates yet to be explored.
  Trying to add an element that has ever been previously added has no effect.
  (We could imagine making this a priority queue if we have a good heuristic for ordering.)
* `verifier_outputs`:  Map[VerificationInput, VerificationResult].
  A cache.  Is only added to, never removed from.
  This cache eliminates the need to pass VerificationResults through the program,
  since they can just be looked up.
* `llm_cache`: Map[LlmInput, List[LlmOutput]]: for efficiency.  Is only added to, never removed
  from.  The input type (the key) is probably a tuple that includes the string sent to the model,
  the model name, and its temperature.  Each value in the map is a list of strings, with length
  `num_llm_samples`.
  * If a vendor (e.g., OpenAI) changes a model without changing its name, than cache entries for it
    need to be removed.

Each access to a global data structure must use locking; or we could store them
persistently, say using SQLite, which permits using multiprocessing rather than
multithreading and could save time across multiple runs.

immutable class ProofState:

* specs: Map[Function, Specification]: the current specification (which may be a guess) for each function.
  * Immutable, so can be represented by `types.MappingProxyType`.
  * When `workstack` is pushed or popped, one entry of the map is updated,
    corresponding to the function that was pushed or popped.  (But, since
    ProofState is immutable, this is by comparison to a previous ProofState.)
  * There might be a specification for a function that is on the workstack.  This is important to
    handle recursion and even when the call graph is a dag rather than a tree.
  * TODO: add information to distinguish verified/assumed/unverified/not-yet processed functions?
* workstack: Stack[WorkItem]
  A stack of functions that need to be (re)processed.
  * Immutable, so can be represented more efficiently than as a Stack.
    It could be a tuple of all the elements, or it could be implemented as a manual linked list, as
    a pair of one element and a pointer to the remainder of the list.
  Invariant:  all the WorkItems with a non-empty `backtrack_hint` are above all the pairs with None.
  This is because every push onto the workstack has a non-None `backtrack_hint`.

Possible fields for ProofState:

* `verified_functions`: a list of functions that have been verified.
* `assumed_functions`: a list of functions with unverified, but trusted, specifications.

immutable class WorkItem:

* `function`: ParsecFunction
* `backtrack_hint`: str
  Each hint is text provided to the LLM to guide it.  I don't have a data
  structure (beyond string) in mind for it yet.
  Example hints:
  * "Please weaken/strengthen the postcondition"
  * "This function is only ever called with non-null values",

immutable class SpecConversation:

* `spec`: Specification
* `conversation`: a conversation history with an LLM, that led to the given spec
* `hint`: Any hints for regenerating specifications, either for repair or for callees.

## Code

```python
def verify_program(program) -> List[Map[Fn, Spec]]:
  """
  The entry point: Verify all the functions in a program.
  Input: a program
  Output: a list of program specifications.  A program specification contains a specification for each function in the program
  """
  # Since workstacks are immutable, a workstack can be represented as a tuple rather than as a Stack.
  initial_workstack: Stack[WorkItem] = all functions in `program`, in reverse topological
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
    Let `top_fn` be the function on the top of the input's workstack.
    The output ProofState has a smaller workstack if top_fn was successfully verified or if top_fn's
    spec will be assumed.
    The output ProofState has a larger workstack (representing backtracking) if `top_fn` was not 
    verified or assumed.
  """
  (fn, backtrack_hint): WorkItem = proofstate.workstack.top();
  new_speccs: List[SpecConversation] = generate_and_repair_spec(fn, backtrack_hint)
  pruned_speccs = prune_heuristically(fn, candidate_speccs, proofstate)

  result = []
  for specc in pruned_speccs:
    # Produce a new ProofState from `specc.spec` and `specc.conversation`.

    # Updating the specs is important even if backtracking will occur.
    next_proofstate_specs = proofstate.specs | {fn: specc.spec}

    last_llm_response = specc.conversation.last()
    if last_llm_response contains "backtrack":
      next_proofstate_workstack =
          proofstate.workstack + [WorkItem(last_llm_response.get_function(), last_llm_response)]
    else:
      next_proofstate_workstack = proofstate.workstack[:-1] # pop off fn
    next_proofstate = ProofState(next_proofstate_specs, next_proofstate_workstack)
    result.append(next_proofstate)
  return result

def generate_and_repair_spec(fn, backtrack_hint) -> List[SpecConversation]:
  """
  Generate a specification for a function.
  Input: a function and hints about how to specify it.  The hints are non-empty only when backtracking.
  Output: a list of potential specs for the function.  Some may verify and some may not verify.
  """
  generated_speccs = generate_speccs(fn, backtrack_hint)
  pruned_specs = prune_heuristically(fn, generated_speccs)
  repaired_specs = [*repair_spec(fn, spec) for spec in pruned_specs]
  return repaired_specs

def prune_heuristically(fn, speccs: List[SpecConversation]) -> List[SpecConversation]:
  # Here is one example of a very simple heuristic for pruning:
  #  * If any spec verifies, return a list containing only the specs that verify.
  #  * Otherwise, return all the specs.

def generate_speccs(fn, backtrack_hint) -> List[SpecConversation]:
  """
  An LLM guesses a specification.
  Input: a function and a hint.  The hint is plaintext.
  Output: a list of candidate specifications of length `num_llm_samples`.
  Implementation note: see LlmSpecificationGenerator.
  """
  llm_input = ("guess the specification for", fn, current_context(fn, proofstate), backtrack_hint)
  specs = llm(llm_input) # call the LLM
  return [SpecConversation(spec, [llm_input]) for spec in specs]

def repair_spec(fn, specc, proofstate) -> List[SpecConversation]:
  """
  Given a specification, iteratively repair it.
  Input: a function and a specification.  The specification may or may not verify.
  Output: a list of repaired specifications (that verify) or a list of faulty specs that have a
          backtracking step associated with them.
  """
  # Implementation note: See `_repair_spec` in `main.py`.
  verified_specs = []

  vresult = call_verifier(fn, specc, proofstate)
  if is_success(vresult):
    verified_specs.append(specc)
    return verified_specs
  
  # specs_to_repair comprises a pair, the first element is a spec, and the second element is a
  # number denoting the number of times a repair was attempted.
  specs_to_repair = queue((specc, 0))
  specs_that_failed_repair = []

  while specs_to_repair:
    spec_under_repair, num_repair_attempts = specs_to_repair.popleft()
    vresult = call_verifier(fn, spec_under_repair, proofstate)
    if is_success(vresult):
      # No need to continue with the current spec under repair, continue with the remainder.
      spec_under_repair.next_step = ACCEPT_VERIFIED_SPEC
      verified_specs.append(spec_under_repair)
      continue

    if num_repair_attempts >= num_repair_iterations:
      # Dead end, repair failed.
      specs_that_failed_repair.append(spec_under_repair)
      continue
  
    # Try repair.
    repair_prompt = get_repair_prompt(spec_under_repair, vresult)
    conversation_with_repair_prompt = spec_under_repair.conversation + repair_prompt
    newly_repaired_specs = call_llm(conversation_with_repair_prompt)

    for newly_repaired_spec, response in newly_repaired_specs:
      next_specc = SpecConversation(
        spec_under_repair,
        newly_repaired_spec,
        conversation_with_repair_prompt + response
      )
      specs_to_repair.append((next_specc, num_repair_attempts + 1))
    
    if verified_specs:
      return verified_specs

    return [
      call_llm_for_backtracking_strategy(
        spec_conversation=unrepairable_spec, proof_state=proof_state)
      for unrepairable_spec in specs_that_failed_repair
    ]

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
