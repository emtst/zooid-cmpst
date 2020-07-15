# Documenting Merge for a Generalisation

## Projection.v

* the generic merge will be a parameter
* the generic merge should have the same type as merge_all (A : eqType -> seq A -> A)
* the fundamental definitions parial_proj and project involve merge_all, hence all the proofs of lemmas involving those must be adapted, mutatis mutandis. This will help us identifying the properties to ask to our generic merge.
* the statement of lemma prjall_merge currently depends on the specific definition of merge; here I see two ways:
  1. we decide that this lemma cannot be rendered gerenric, hence we state and prove it again and again for each instance of the generic merge, or
  2. we identify a property that has to hold for all possible generic merges, that relates the continuation and its merge (maybe something like subtyping); however in this case the lemma would be an "axiom" (we would need to ask that the generic merge has the property).
