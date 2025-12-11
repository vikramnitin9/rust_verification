# Algorithm for verifying a program using LLMs and a verifier (e.g., CBMC)

Overall idea:  The algorithm verifies a program by verifying one function at a time, generally in reverse topological order.

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
of proof states.  The implementation explores all of these possibilities in
parallel.

## Parameters

Two integers parameterize the algorithm:

* num_llm_samples: each call to `llm()` returns a list of this length.
  As a general rule, after each call to `llm()`, a the list is heuristically pruned to reduce the exploration space.
* num_repair_iterations: the number of times that the LLM tries to repair a specification, using feedback from running the verifier.

The implementation also contains:

* the model temperature, which cannot be set to 0 for sampling.

## Data structures

immutable class VerificationInput:
* function
* spec for function
* context: specifications provided to this verification run, created by calling `current_context()`.  It includes:
  * a spec for each of the function's callees
  * a spec for each global variable that the function uses
  * optionally, facts about how the function is called, such as constraints on what values are passed to it.

immutable class VerificationResult:

* input: VerificationInput
* succeeded: boolean
* failure_messages: String | None

It doesn't make sense to say that a function specification in isolation is
verified or not, because the verification result depends on the full verifier
input, which includes the specifications of the callees and callers.

Global data structures:

* verifier_outputs:  Map[VerificationInput, VerificationResult].
  A cache for efficiency.  Is only added to, never removed from.
  This cache eliminates the need to pass VerificationResults through the program,
  since they can just be looked up.
* llm_cache: Map[LlmInput, LlmOutput]: for efficiency.  Is only added to, never removed from.
  The input and output types are probably String.
* proofstates_worklist:  set of ProofStates yet to be explored.
  Trying to add an element that has ever been previously added has no effect.
  (We could imagine making this a priority queue if we have a good heuristic for ordering.)

Each access to a global data structure must use locking; or we could store them persistently, say using SQLite, which permits using multiprocessing rather than multithreading and could save time across multiple runs.

class ProofState:
* specs: Map[fn, spec]: the current specification (which may be a guess) for each function.
* workstack: Stack[(function, hints)]
  A stack of functions that need to be (re)processed.
  Each hint is text provided to the LLM to guide it.  I don't have a data structure (beyond string) in mind for it yet.
Possible fields:
* verified_functions: a list of functions that have been verified.
* assumed_functions: a list of functions with unverified, but trusted, specifications.

```pseoudocode
// The entry point: Verify all the functions in a program.
// Input: a program
// Output: a specification for each function in the program
verify_program(program) -> Map[Fn, Spec]:
  initial_workstack: Stack[(function, hints)] = all functions in `program`, in reverse topological
                                                order (that is, children first), with empty hints.
  initial_ps = ProofState(initial_workstack)
  global.proofstates_worklist.add(initial_ps)
  while global.proofstates_worklist not empty:
    ps = global.proofstates_worklist.remove_first()
    next_proofstates = step(ps)
    for next_ps in next_proofstates:
      if next_ps.workstack is empty:
        // TODO: We might not want to greedily return the first completed
        // ProofState, because it might represent assuming every spec.
        return next_ps
      else:
        global.proofstates_worklist.add(next_ps)

// Given a ProofState, tries to verify the function at the top of the workstack.
// This is the key unit of parallelism.
// Input: a ProofState
// Output: a list of ProofStates resulting from the verification attempt.
//   Let f be the top of the input's workstack.
//   The output ProofState has a smaller workstack if f was successfully verified or if f's spec will be assumed.
//   The output ProofState has a larger workstack (representing backtracking) if f was not successfully verified.
step(ps: ProofState) -> List[ProofState]:
  (fn, hints) = ps.workstack.top();
  specs_for_fn: [(spec, vresult)] = try_to_specify(fn, hints)
  next_steps: [(spec, BacktrackInfo)] = choose_next_step(fn, specs_for_fn)
  result = []
  for (spec, backtrack_to) in next_steps:
    next_ps = ps.clone()
    next_ps.specs[fn] = spec
    if backtrack_to != None:
      next_ps.workstack.push(backtrack_to.function)
    else
      next_ps.workstack.pop() // pop off fn
    result += next_ps
  return result

// Generate a specification for a function.
// Input: a function and hints about how to specify it.  The hints are non-empty only when backtracking.
// Output: a list of potential specs for the function.  Some may verify and some may not verify.
try_to_specify(fn, hints) -> List[spec]:
  generated_specs = generate_specs(fn, hint)
  // Here is one example of a very simple heuristic for pruning:
  //  * it any spec verifies, return a list containing only it.
  //  * otherwise, return all the specs.
  pruned_specs = prune_heuristically(fn, generated_specs)
  repaired_specs = [*repair_spec(fn, spec) for spec in pruned_specs]
  return repaired_specs

// An LLM guesses a specification.
// Input: a function and a hint.  The hint is plaintext.
//   (Maybe also input a list of specifications that have been generated in the past, to avoid
//   repeated work??  But we do want to explore new combinations of previous guesses.)
//   James notes:  I don't think we can get around the LLM potentially returning the same specs it
//   generated.  By including previously-generated specs in the prompt, we might be able to steer it
//   toward avoiding duplicates, but the only way to be sure is if we filter out the duplicates from
//   the response.  I.e., we can't avoid the work done by the model.
// Output: a list of candidate specifications of length `num_llm_samples`.
// Implementation note: see LlmSpecificationGenerator.
generate_specs(fn, hint) -> List[spec]:
  specs = llm("guess the specification for", fn, proofstate, hint) // call the LLM
  return specs

// Given a specification, iteratively repair it.
// Input: a function and a specification.  The specification may or may not verify.
// Output: a list of repaired specifications.  Each may or may not verify.
// Implementation note: See `_get_repaired_specification` in `generate_specs.py`.
repair_spec(fn, spec, proofstate) -> [Spec]:
  all_specs = []  // Return every spec that was observed ...
  verified_specs = []  // ... unless some were verified, in which case return only them.
  current_specs = [spec]
  for i = 1 to num_repair_iterations:
    next_specs = []
    for spec in current_specs: 
      if spec in all_specs:
        // We have already seen this spec, so don't re-process it.
        continue
      all_specs += spec
      vresult = call_verifier(fn, spec, proofstate) // e.g., CBMC
      if is_success(vresult):
        verified_specs += vresult
        continue
      next_specs += spec
    specs = [*llm("repair the specification", fn, spec, vresult) for spec in next_specs]
    // TODO: perhaps prune out duplicates, for efficiency.
  if verified_specs:
    return verified_specs:
  else:
    return all_specs

// Calls a verification tool such as CBMC.
// Input: the function, a specification, and context.
// Output: a verification result.
// Implementation note: Uses a cache to avoid recomputation.
call_verifier(fn, spec, proofstate) -> VerificationResult:
  context = current_context(fn, proofstate)
  vinput = VerificationInput(fn, spec, context)
  vresult = global.verifier_outputs[vinput]
  if vresult == None:
    vresult = CBMC(fn, spec, context)
    global.verifier_outputs[vinput] = vresult
  return vresult

// Input: A function
// Output: the function's current verification context: the specs of callers and callees.
current_context(fn, proofstate) -> context:
  // Look up from proofstate's fields, such as `specs` or `verified_functions` and `assumed_functions`.

// Choose the next step for the overall algorithm: continue or backtrack.
// Input: A function and a list of candidate specifications for it.
// Output: A list of pairs of (specification, an indication of whether to backtrack).
// Implementation note: The system currently returns a singleton list of the first specification that verifies.
choose_next_step(fn, candidate_specs: List[spec], proofstate) -> [(spec, backtrack_info)]
  pruned_specs = prune_heuristically(fn, candidate_specs, proofstate)
  result = []
  for spec in pruned_specs:
    vresult = call_verifier(fn, spec, proofstate)
    If vresult.is_success:
      backtrack_info = None
    else:
      // Enhancement ideas:
      // Also provide all the candidate specs, rather than just the one chosen by the heuristic?
      // Or choose a spec and provide backtracking hints in a single heuristic rather than separating them?
      // Or permit this LLM call to return a different spec from candidate_specs than the heuristic chose?
      backtrack_info = llm("choose a callee to repair, and provide hints", fn, spec, vresult)
    result += (spec, backtrack_info)
  return result
```

Suppose that, after creating a VerificationInput, the system changes some
specification in the context.  Then the old VerificationInput is no longer
applicable.  A call to `call_verifier()` will create a new VerificationInput
and the verifier will be re-run.  (This is one reason that verification
results are not passed around in the algorithm, but are re-computed -- to
avoid the bookkeeping of figuring out what has to be updated.)

## Parallelization

Many for loops and list comprehensions (but not the for loop in `repair`) can be parallelized.

## OLD, NO LONGER RELEVANT

More about forking processes:

At each point that the LLM is invoked, the algorithm could call the LLM multiple times and pursue each of the possibilities (possibly in parallel).
Currently this is hard-coded in `try_to_specify()`, which is the client of `generate_specs()` which calls the LLM to produce multiple results.
However, it is not done for other LLM calls in `repair_spec()` and `choose_next_step()`.

It would be better for the algorithm to apply sample-exploration more uniformly.
* One way is to hard-code the other LLM uses, just as `generate_specs()` and its client `try_to_specify()` are.
* Another way is to modify the algorithm to fork multiple processes, like so:
  * Rewrite the algorithm to treat each LLM query call as returning exactly one value.  (This actually simplifies `try_to_specify()` and its client `verify_program()`.
  * Actually, each LLM query returns a list (which is different than the above rewriting).
    Fork N processes, one for for each element of the list.
    Each forked process has its own process state, which starts as a copy of the global variables and call stack.
  * Pruning processes:
    Whenever a process successfully completes a task (I'm not exactly sure what is the definition of "task" here), possibly prune all the siblings of this process that are still running, because they are no longer needed.
    This is similar to a process manager that prunes processes that have been superseded (that, is prune a process if some other process already solved the problem).
    A process manager would also prune processes that have run for too long.

LocalWords:  workstack llm num VerificationInput VerificationResult boolean fn
LocalWords:  VerificationResults LlmInput LlmOutput proofstates ProofStates ps
LocalWords:  ProofState TODO f's vresult BacktrackInfo plaintext proofstate py
LocalWords:  LlmSpecificationGenerator recomputation vinput
