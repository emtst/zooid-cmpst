# Documenting Merge for a Generalisation

## Projection.v

### Recursive projection and partial projection
```
  {
  Fixpoint merge (A: eqType) (oL : A) (K : seq A) :=
    match K with
    | [::] => Some oL
    | h::t => if h == oL then merge oL t
              else None
    end.
  }
```
* the generic merge will be a parameter
* the generic merge should have the same type as `merge_all` (`TyMerge := A : eqType -> seq A -> A`), or maybe, since the idea was of a relation see below `Merge`, for coinductive projection
* the fundamental definitions `partial_proj` and project involve `merge_all`, hence all the proofs of lemmas involving those must be adapted accordingly. This will help us identifying the properties to ask to our generic merge.
* the statement of lemma `prjall_merge` currently depends on the specific definition of merge; here I see two ways:
  1. we decide that this lemma cannot be rendered gerenric, hence we state and prove it again and again for each instance of the generic merge, or
  2. we identify a property that has to hold for all possible generic merges, that relates the continuation and its merge (maybe something like subtyping); however in this case the lemma would be an "axiom" (we would need to ask that the generic merge has the property).
* Same as for `prjall_merge`: `projectmsg_var`, `pprojall_merge`
* `pprojall_some`: this is very specific, maybe just erase this
* again, other lemmas should work mutatis mutandis

### Coinductive projection
```
  {
  Definition Merge (F : lbl /-> mty * rl_ty) (L : rl_ty) : Prop :=
    forall Lb Ty L', F Lb = Some (Ty, L') -> EqL L' L
  }
```
* Merge has already the type of a relation
* `Proj_` and `Project` should be OK with the new merge
* all the lemmas, up to `project_unroll` included, should maintain the same statement, proofs should work mutatis mutandis
* `lunroll_merge`, statement to be adapted to the new type of the generic `merge`
* all the lemmas, up to `lunroll_end` included, should maintain the same statement, proofs should work mutatis mutandis
* `merge_equal` definitely will not hold
* all other lemmas and definitions should mantain the same statement, proofs should work mutatis mutandis

## TraceEquiv.v

* `Proj_None_next` uses `IProj_mrg_inv` and the fact that `Merge` is defined with an "extensional" equality on continuations (`EqL`)
* In `iproj_end`, `Merge` appears in a case analysis, however it looks like that such a property will hold easily for every merge relation we pick
* In `IProj_unr`, `Merge` appears in the 4th induction case, but only `iprj_mrg` (constructor for `IProj`) is used; this would be defined the same way, but with the generic merge.
* In `Projection_send` a case is solved by calling `EqL_IProj` with the hypothesis of `Merge something something`; this directly exploits the fact that `Merge` is defined via extensional equality. We might need some lemma that substitutes `EqL_IProj`... something like `Merge C L -> Merge C L' -> IProj G L -> IProj G L'`. For many definitions of `Merge` I guess that more will hold: that `Merge C L -> Merge C L' -> EqL L L'` that we will be able to directly compose with `EqL_IProj`.
* `Projection_unr` call IProj_unr and uses `Merge`. Everything should work also with a different merge. 
* `Proj_recv_undo` call prj_mrg and uses `Merge`. Everything should work also with a different merge.
* `runstep_proj` uses `Proj_recv_undo` (see above).
* `Project_gstep_proj` uses `runstep_proj` (see above).
* In `CProj_step`, while proving an intermediate goal, again we use directly the fact that `Merge` is defined as `EqL` of the continuations; that is needed for `EqL_Project`, similar to `EqL_IProj`, about a possible approach for the solution see above the comment about `Projection_send`.
* In `Project_gstep`, while proving an intermediate goal, again we use directly the fact that `Merge` is defined as `EqL` of the continuations; that is needed `EqL_IProj`, about a possible approach for the solution see above the comment about `Projection_send`.
* The final main theorem for step soundness, step completeness and trace equivalence rely on `Merge`, only via the results already mentioned; it should be possible to keep the current statements
* all non-mentioned lemmas and definitions should work smoothly



