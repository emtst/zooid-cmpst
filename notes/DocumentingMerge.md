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
* the fundamental definitions `parial_proj` and project involve `merge_all`, hence all the proofs of lemmas involving those must be adapted accordingly. This will help us identifying the properties to ask to our generic merge.
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


