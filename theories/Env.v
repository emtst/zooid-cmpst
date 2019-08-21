From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import MPST.Atom.

(* Set Printing All. *)

Module Type ENTRY.

  Parameter K : eqType.
  Parameter V : eqType.

End ENTRY.

Module Type ENV (En : ENTRY).
  Parameter env : Type.

  Parameter eq_env : env -> env -> bool.
  Parameter eq_envP : Equality.axiom eq_env.

  Canonical env_eqMixin := EqMixin eq_envP.
  Canonical env_eqType := Eval hnf in EqType env env_eqMixin.

  Parameter empty : env.

  Parameter def : env -> bool.
  Parameter undef : env -> bool.

  (* some operations *)
  Parameter upd : En.K -> En.V -> env -> env.
  Parameter add_upd : En.K -> En.V -> env -> env.
  Parameter add : En.K -> En.V -> env -> env.
  Parameter look : En.K -> env -> option En.V.
  Parameter rem : En.K -> env -> env.
  Parameter dom : env -> seq En.K.

  Parameter dom_pred : env -> pred En.K.
  Parameter in_domP : forall (x : En.K) (E : env),
      reflect (exists v : En.V, look x E = Some v) (x \in dom E).

  Parameter look_add : forall (a : En.K) (T : En.V) (D : env),
      def (add a T D) -> look a (add a T D) = Some T.

  Parameter look_add_deep : forall (a a' : En.K) (T : En.V) (D : env),
      a != a' -> def (add a T D) -> look a' (add a T D) == look a' D.

  Parameter look_not_some :
    forall (x : En.K) (D : env), ~ (exists v : En.V, look x D = Some v) -> look x D = None.
  Inductive look_spec (x : En.K) (D : env) : bool -> Prop :=
    look_some : forall v : En.V, look x D = Some v -> look_spec x D true
  | look_none : look x D = None -> look_spec x D false.

  Parameter domP : forall (x : En.K) (D : env), look_spec x D (x \in dom D).
  Parameter singleton_def : forall (k : En.K) (v : En.V), def (add k v empty).
  Parameter in_dom_def : forall (a' : En.K) (D : env), a' \in dom D -> def D.
  Parameter dom_add :
    forall (k : En.K) (v : En.V) (E : env),
      def (add k v E) -> dom (add k v E) =i predU (pred1 k) (mem (dom E)).
  Parameter rem_add_id :
    forall (k' : En.K) (v' : En.V) (D : env), def (add k' v' D) -> D = rem k' (add k' v' D).
  Parameter rem_add :
    forall (k k' : En.K) (v : En.V) (D : env), k != k' -> rem k' (add k v D) = add k v (rem k' D).
  Parameter add_rem_id :
    forall (x : En.K) (v : En.V) (E : env), look x E == Some v -> add x v (rem x E) = E.
  Parameter in_dom_rem :
    forall (c c' : En.K) (D : env), (c \in dom (rem c' D)) = (c != c') && (c \in dom D).
  Parameter in_dom_add :
    forall (c c' : En.K) (T : En.V) (D : env),
      (c \in dom (add c' T D)) = def (add c' T D) && ((c == c') || (c \in dom D)).
  Parameter in_dom_upd :
    forall (c c' : En.K) (T : En.V) (D : env),
      (c \in dom (upd c' T D)) = def D && (c == c') || (c \in dom D).
  Parameter def_nested : forall (a : En.K) (t : En.V) (E : env), def (add a t E) -> def E.
  Parameter def_diff_value :
    forall (x : En.K) (t t' : En.V) (E : env), def (add x t E) -> def (add x t' E).
  Parameter in_add_undef :
    forall (k : En.K) (t : En.V) (E : env), def E -> undef (add k t E) <-> k \in dom E.
  Parameter add_twice : forall (k : En.K) (t t' : En.V) (E : env), undef (add k t (add k t' E)).
  Parameter def_add_twice :
    forall (k k' : En.K) (t t' : En.V) (E : env), def (add k t (add k' t' E)) -> k != k'.
  Parameter rem_swap : forall (k k' : En.K) (E : env), rem k (rem k' E) = rem k' (rem k E).
  Parameter dom_nested :
    forall (a b : En.K) (t : En.V) (E : env),
      def (add b t E) -> a \in dom E -> a \in dom (add b t E).
  Parameter filter_by_key : pred En.K -> env -> env.

  Parameter filter_by_key_nil : forall pr : pred En.K, filter_by_key pr empty == empty.
  Parameter partition_by_key : pred En.K -> env -> env * env.
  Parameter map_on_keys' : (En.K -> En.K) -> env -> env.
  Parameter map_on_keys : (En.K -> En.K) -> env -> env.

  Parameter intersection : env -> env -> env.
  Parameter difference : env -> env -> env.
  Parameter disjoint : env -> env -> bool.
  Parameter union : env -> env -> env.

  Notation "A --- B" := (difference A B)  (at level 80, right associativity). (* : env_scope. *)
  Notation "A /:\ B" := (intersection A B) (at level 80, right associativity). (* : env_scope. *)
  Notation "A \:/ B" := (union A B) (at level 80, right associativity). (* : env_scope. *)

  Parameter unionA : associative union.
  Parameter disjointC : commutative disjoint.
  Parameter union_empty : forall (D : env), D = (D \:/ empty).
  Parameter disjoint_wkn : forall E1 E2 E3 : env, disjoint E1 (E2 \:/ E3) -> disjoint E1 E2.
  Parameter disjoint_diff_inter : forall D D' : env, def D -> def D' -> disjoint (D---D') (D /:\ D').
  Parameter union_def : forall E1 E2, def (E1 \:/ E2) -> def E1 /\ def E2.
  Parameter disjoint_diff_comm : forall D D', def D -> def D' -> disjoint (D---D') (D' --- D).
  Parameter diff_empty : forall A, def A -> (empty --- A) = empty.

  Definition split (E1 E2 : env) : env * env * env := (E1 --- E2, E1 /:\ E2, E2 --- E1).
  Parameter update_all_with : En.V -> env -> env.

  Definition binds a T (D : env) : bool := (look a D) == Some T.
  Parameter binds_add : forall a b T T' D,
      binds a T D -> def (add b T' D) -> binds a T (add b T' D).
  Parameter binds_next : forall x y S S' G,
      y != x -> binds y S' (add x S G) -> binds y S' G.
  Parameter binds_top_add : forall a T D,
      def (add a T D) -> binds a T (add a T D).
  Parameter def_add : forall k t E,
      def (add k t E) <-> k \notin dom E /\ def E.
  Parameter in_addb : forall x k v D,
      x \in dom (add k v D)
            = (k \notin dom D) && (def D && (x == k) || (x \in dom D)).

  Parameter in_add : forall k k' t E,
      def (add k' t E) ->
      k \in dom (add k' t E) = (k == k') || (k \in dom E).
  Parameter dom_add' : forall k t E, def(add k t E) -> dom (add k t E) =i k :: dom E.
  Parameter dom_diff_eq : forall (k : En.K) (v : En.V) v' D, dom (add k v D) = dom (add k v' D).
  Parameter notin_add : forall k k' T D,
      def (add k' T D) -> k \notin dom (add k' T D) = ((k != k') && (k \notin dom D)).
  Parameter add_union : forall k T D D',
      ((add k T D) \:/ D') = (add k T (D \:/ D')).
  Parameter dom_union : forall D1 D2 k,
      (k \in dom (D1 \:/ D2)) =
      def (D1 \:/ D2) && ((k \in dom D1) || (k \in dom D2)).
  Parameter dom_update_all_with : forall T D, dom (update_all_with T D) =i dom D.
End ENV.

Module Env (En : ENTRY) : ENV En.
  Definition env := seq (En.K * En.V).

  Definition eq_env : env -> env -> bool. Admitted.
  Definition eq_envP : Equality.axiom eq_env. Admitted.

  Canonical env_eqMixin := EqMixin eq_envP.
  Canonical env_eqType := Eval hnf in EqType env env_eqMixin.

  Definition empty : env := [::].
  Definition def (E : env) := uniq (map fst E).
  Definition undef E := negb(def E).

  Definition dom (E : env)  : seq En.K := if def E then map fst E else [::].

  Definition dom_pred (E : env) : pred En.K := mem (dom E).


  (* update if present *)
  Definition upd x t (E : env) :=
    map (fun en => if x == fst en then (x, t) else en) E.

  (* update or insert *)
  Definition add_upd x t (E : env) : env:=
    if x \in dom E then upd x t E else (x , t) :: E.

  Fixpoint look x (E : env) : option En.V :=
    match E with
    | nil => None
    | (x', t) :: E => if x == x' then Some t else look x E
    end
    .

  Definition add x t (E : env) : env := add_upd x t E.

  Definition rem x (E : env) : env := filter (fun en => x != fst en) E.

  Lemma in_domP x E : reflect (exists v, look x E = Some v) (x \in dom E).
  Admitted.

  (***************************************************************************************)
  Lemma look_not_some x D : ~ (exists v, look x D = Some v) -> look x D = None.
  Admitted.

  Inductive look_spec x D : bool -> Prop :=
  | look_some v : look x D = Some v -> look_spec x D true
  | look_none : look x D = None -> look_spec x D false.

  Lemma domP x D : look_spec x D (x \in dom D).
  Proof.
    case: in_domP=>[|/look_not_some].
    + move=>[v]; apply: look_some.
    + apply: look_none.
  Qed.

  Lemma singleton_def k v : def (add k v empty). (* stays *)
  Proof.
    by rewrite/def/add.
  Qed.

  Lemma in_dom_def a' D: a' \in dom D -> def D. (* stays *)
  Proof.
    unfold dom.
    case (def D)=>//.
  Qed.

  (* Properties of defined environments *)
  Lemma look_add a T D: def (add a T D) -> look a (add a T D) = Some T.
  Admitted.

  Lemma look_add_deep a a' T D: a != a' -> def (add a T D) -> look a' (add a T D) == look a' D.
  Admitted.


  Lemma dom_add k v (E : env) : def (add k v E) ->
                                dom (add k v E) =i predU (pred1 k) (mem (dom E)).
  Admitted.


  Lemma rem_add_id k' v' D : def (add k' v' D) -> D = rem k' (add k' v' D).
  Admitted.


  Lemma rem_add k k' v D : k != k' -> rem k' (add k v D) = add k v (rem k' D).
  Admitted.

  Lemma add_rem_id x v E : look x E == Some v -> add x v (rem x E) = E.
  Admitted.

  Lemma in_dom_rem c c' D :
    c \in dom (rem c' D) = (c != c') && (c \in dom D).
  Admitted.

  Lemma in_dom_add c c' T D :
    c \in dom (add c' T D) = def (add c' T D) && ((c == c') || (c \in dom D)).
  Admitted.

  Lemma in_dom_upd c c' T D :
    c \in dom (upd c' T D) = def D && (c == c') || (c \in dom D).
  Admitted.

  Lemma def_nested a t E: def (add a t E) -> def E.
  Admitted.

  Lemma def_diff_value (x : En.K) (t t' : En.V) E: def (add x t E) -> def (add x t' E).
  Admitted.

  Lemma in_add_undef k t E: def E -> undef (add k t E) <-> k \in dom E.
  Proof.
  Admitted.

  Lemma add_twice k t t' E : undef(add k t (add k t' E)).
  Admitted.

  Lemma def_add_twice k k' t t' E : def(add k t (add k' t' E)) -> k != k'.
  Admitted.

  Lemma rem_swap k k' E:
    rem k (rem k' E) = rem k' (rem k E).
  Admitted.

  (* no longer true *)
  (* Lemma add_swap k k' t s E: *)
  (*   add k t (add k' s E) = add k' s (add k t E). *)
  (* Proof. *)
  (*   case: E=>// f. *)
  (*   rewrite /add !fun_if /= !in_nil !supp_ins !inE. *)
  (*   case: (suppP k f)=>[v|]fnd_k_f; case: (suppP k' f)=>[v'|]fnd_k_f'=>//. *)
  (*   + by rewrite orbC. *)
  (*   + by rewrite orbC. *)
  (*   + rewrite !Bool.orb_false_r; case: ifP; rewrite eq_sym=>H; rewrite H //. *)
  (*     by congr Def; rewrite ins_ins H. *)
  (* Qed. *)

  Theorem dom_nested a b t E : def (add b t E) -> a \in dom E -> a \in dom (add b t E).
  Admitted.

  (* lemma about finmaps that we are trying to get away from *)
  (* Definition ckey : K * V -> K := fst. *)
  (* (* a lemma about finmaps *) *)
  (* Definition sorted_filter_by_pred s (p : pred K) : *)
  (*   sorted ord (map key s) -> sorted ord (map key (filter (preim ckey p) s)). *)
  (* Proof. *)
  (*   move=>H ; rewrite -filter_map path.sorted_filter //. *)
  (*   by apply: trans. *)
  (* Defined. *)

  Definition filter_by_key (pr : pred En.K) (E: env) : env := filter (fun en => pr (fst en)) E.

  Lemma filter_by_key_nil (pr : pred En.K) : filter_by_key pr nil == nil.
  Proof.
    by [].
  Qed.

  Definition partition_by_key (pr : pred En.K) (E: env) : env * env :=
    (filter_by_key pr E, filter_by_key (predC pr) E).

  Fixpoint map_on_keys' (f : En.K -> En.K) (s : seq (En.K * En.V)) : seq (En.K * En.V) :=
    map (fun en => (f (fst en), snd en)) s.

  Definition map_on_keys (f : En.K -> En.K) (E : env) : env :=
    if def E
    then map_on_keys' f E
    else [::]. (* TODO do we need this? this must be wrong because it
    makes an undef thing def (the empty list is def) *)

  Lemma filter_preserves_def E p : def E -> def (filter_by_key p E).
  Abort. (* desired property, prove if actually needed *)

  Definition intersection (E E' : env) : env :=
    filter_by_key (fun k => k \in dom E') E.

  Definition difference (E E' : env) : env :=
    filter_by_key (fun k => k \notin dom E') E.

  Definition disjoint (E E' : env) : bool :=
    all (predC (fun x => x \in dom E)) (dom E').

  Definition union (E E' : env) : env :=
    E ++ E'.

  Lemma disjoint_nil : disjoint empty empty.
  Proof.
    by [].
  Qed.

  Notation "A --- B" := (difference A B)  (at level 80, right associativity). (* : env_scope. *)
  Notation "A /:\ B" := (intersection A B) (at level 80, right associativity). (* : env_scope. *)
  Notation "A \:/ B" := (union A B) (at level 80, right associativity). (* : env_scope. *)

  Lemma unionC : commutative union.
  Abort. (* this lemma does not hold anymore *)

  Lemma union_undef E E' E'': (E \:/ E') = E'' -> undef E' -> undef (E \:/ E').
  Abort. (* adapted from the old lemma, but it's not clear we need this lemma *)

  Lemma unionA : associative union.
  Admitted.

  Lemma disjointC : commutative disjoint.
  Admitted.

  Lemma union_empty D : D = (D \:/ empty).
  Proof.
    elim D=>// f ; rewrite/union=>/=.
    rewrite/empty=>// l H.
    by rewrite cats0.
  Qed.

  Lemma disjoint_union_def E1 E2:
    disjoint E1 E2 = def(E1 \:/ E2).
  Abort. (* does not hold anymore (needs E1 and E2 to be defined) *)

  Lemma disjoint_wkn E1 E2 E3: disjoint E1 (E2 \:/ E3) -> disjoint E1 E2.
  Admitted.

  Lemma disjoint_diff_inter D D' :
    def D -> def D' -> disjoint (D---D') (D /:\ D').
  Admitted.

  Lemma union_def E1 E2: def (E1 \:/ E2) -> def E1 /\ def E2.
  Admitted.

  Lemma disjoint_union_3 E1 E2 E3:
    disjoint E1 E2 /\ disjoint E2 E3 /\ disjoint E1 E3 <-> def(E1 \:/ E2 \:/ E3).
  Abort. (* no longer the case as the -> direction fails *)

  Lemma disjoint_diff_comm D D' :
    def D -> def D' -> disjoint (D---D') (D' --- D).
  Admitted.

  Lemma diff_empty A: def A -> (empty --- A) = empty.
    case: A => // f; rewrite/nil/difference/filter_by_key=>//.
  Qed.

  Definition split (E1 E2 : env) : env * env * env :=
    (E1 --- E2, E1 /:\ E2, E2 --- E1).

  Definition update_all_with (v : En.V) (E : env) : env :=
    map (fun el => (fst el, v)) E.

  Definition binds a T (D : env) : bool :=
    (look a D) == Some T.

  Lemma binds_add a b T T' D:
    binds a T D -> def (add b T' D) ->
    binds a T (add b T' D).
  Admitted.

  Lemma add_binds a b T T' D:
    binds a T D -> a!=b -> def (add b T' D) -> binds a T (add b T' D).
  Abort. (* this lemma is silly as from binds a T D -> def (add b T' D) we can show that a != b *)

  Lemma binds_next x y S S' G:
    y != x ->
    binds y S' (add x S G) ->
    binds y S' G.
  Admitted.

  Lemma binds_top_add a T D:
    def (add a T D) ->
    binds a T (add a T D).
  Proof.
    rewrite/add/add_upd.
    case (a \in dom D).
    admit. (* lemma about update *)
    by rewrite/binds/look eq_refl.
  Admitted.

  Lemma binds_def a T D:
    binds a T D -> def D.
  Abort. (* no longer holds (binds finds the first if it is duplicated/undefined)*)

  (* TODO remove this: it is the same thing as binds *)
  (* Definition isin a (D : env) : bool := *)
  (*   if look a D is Some _ then true else false. *)

  (* TODO add indom here *)

  Lemma def_add k t E:
    def (add k t E) <-> k \notin dom E /\ def E.
  Admitted.


  Lemma look_addb a b T (D : env) : look a (add b T D)
                                    = if def (add b T D)
                                      then if a == b then Some T else look a D
                                      else None.
  Abort. (* no longer holds, look would return something from undef envs *)


  Lemma def_add_cancel k v v' E E' :
    def (add k v E) -> add k v E = add k v' E' -> v = v' /\ E = E'.
  Abort. (* it should be provable, but it is not needed in this style *)


  Lemma in_addb x k v D :
    x \in dom (add k v D)
          = (k \notin dom D) && (def D && (x == k) || (x \in dom D)).
  Admitted.

  Lemma in_add k k' t E:
    def (add k' t E) ->
    k \in dom (add k' t E) = (k == k') || (k \in dom E).
  Admitted.

  Lemma dom_add' k t E : def(add k t E) -> dom (add k t E) =i k :: dom E.
  Admitted.

  Lemma dom_diff_eq (k : En.K) (v : En.V) v' D : dom (add k v D) = dom (add k v' D).
  Admitted.

  Lemma notin_add k k' T D:
    def (add k' T D) -> k \notin dom (add k' T D) = ((k != k') && (k \notin dom D)).
  Admitted.

  Lemma add_union k T D D':
    ((add k T D) \:/ D') = (add k T (D \:/ D')).
  Admitted.

  Lemma dom_union D1 D2 k :
    (k \in dom (D1 \:/ D2)) =
    def (D1 \:/ D2) && ((k \in dom D1) || (k \in dom D2)).
  Admitted.

  Lemma dom_update_all_with T D : dom (update_all_with T D) =i dom D.
  Proof.
    by rewrite/update_all_with/dom/def -map_comp /comp=>/=.
  Qed.

  Definition subst_env c c' D := (* this is upd *)
    match look c D with
    | Some T => add c' T (rem c D)
    | None => D
    end.

  (* TODO: continue importing lemmas from OldEnv.v from CONTINUE HERE and on *)

  (* Lemma subst_envK c D : subst_env c c D = D. *)
  (* Proof. *)
  (*   case: D=>//f; rewrite /subst_env/look/add/rem/upd/dom supp_rem !inE eq_refl /=. *)
  (*   case: (suppP c f)=>[v|] H; rewrite H //. *)
  (*   rewrite ins_rem eq_refl; congr Def; move: H. *)
  (*   (* FIXME: lift as lemma to finmap.v *) *)
  (*   elim/fmap_ind': f =>// k v' f path_k IH. *)
  (*   rewrite fnd_ins ins_ins; case: ifP=>//; first by move=> /eqP-> []->. *)
  (*     by move=> _ fnd_c; rewrite IH. *)
  (* Qed. *)

  (* Lemma neq_add_substC x y z T D : *)
  (*   x != y -> add x T (subst_env y z D) = subst_env y z (add x T D). *)
  (* (* Proof. *) *)
  (* (*   case: D =>// f neq; rewrite /subst_env look_addb def_addb andbC /dom/look. *) *)
  (* (*   rewrite eq_sym (negPf neq); case: suppP =>[v|]-H //. *) *)
  (* (*   + rewrite /def/andb/negb; case: (suppP y f) =>[v'|]-H'; rewrite H'. *) *)
  (* (*     by rewrite add_swap -rem_add // [add x _ _]/add/dom (in_supp_fnd (introT eqP H)). *) *)
  (* (*     by rewrite [add x _ _]/add/dom (in_supp_fnd (introT eqP H)). *) *)
  (* (*   + rewrite /def/negb/andb rem_add //. *) *)
  (* (*     case: (suppP y f) =>[v'|]-H'; rewrite H' //. *) *)
  (* (*     by rewrite add_swap. *) *)
  (* (* Qed. *) *)
  (* Admitted. *)

  (* Lemma look_rem x k D : look x (rem k D) = if x == k then None else look x D. *)
  (* Proof. *)
  (*   case: D=>/=; first by case: ifP. *)
  (*   move=> f; by apply: fnd_rem. *)
  (* Qed. *)

  (* Lemma upd_rem_absorv x T D : *)
  (*   upd x T (rem x D) = upd x T D. *)
  (* Proof. *)
  (*   case: D=>// f; rewrite /rem/upd; congr Def. *)
  (*   by rewrite ins_rem eq_refl. *)
  (* Qed. *)

  (* Lemma add_rem_absorv x T D : *)
  (*   x \notin dom D -> add x T (rem x D) = add x T D. *)
  (* Proof. *)
  (*   rewrite /add in_dom_rem eq_refl /= =>/negPf->. *)
  (*   by rewrite upd_rem_absorv. *)
  (* Qed. *)

  (* Lemma look_some_in x v D : look x D = Some v -> x \in dom D. *)
  (* Proof. by move => /(ex_intro _ v)/in_domP. Qed. *)

  (* Lemma look_none_in x D : look x D = None -> x \notin dom D. *)
  (* Proof. by case: domP=>[v|]->. Qed. *)

  (* Lemma rem_substC x y z D : *)
  (*   y != x -> z != x -> *)
  (*   subst_env y z (rem x D) = rem x (subst_env y z D). *)
  (* Proof. *)
  (*   rewrite /subst_env look_rem eq_sym=>/negPf->. *)
  (*   case:(domP y D )=>[v|]H; rewrite H // => xz. *)
  (*   by rewrite rem_swap -rem_add. *)
  (* Qed. *)

  (* Lemma eq_add_substC x y T D : *)
  (*   def (add x T D) -> *)
  (*   add y T (subst_env x y D) = subst_env x y (add x T D). *)
  (* Proof. *)
  (*   case: D=>//f Df; rewrite /subst_env; rewrite look_add /look=>//. *)
  (*   have c1f: x \notin supp f by move: Df; rewrite def_addb=>/andP-[]. *)
  (*   by rewrite (fnd_supp c1f) -rem_add_id. *)
  (* Qed. *)

  (* Lemma subst_addC x y z T D : *)
  (*   def (add z T D) -> *)
  (*   add (if z == x then y else z) T (subst_env x y D) *)
  (*   = subst_env x y (add z T D). *)
  (* Proof. *)
  (*   case: (boolP (x == z)) =>[/eqP->|]. *)
  (*   + by rewrite eq_refl; apply: eq_add_substC. *)
  (*   + by rewrite eq_sym=>neq Df; rewrite (negPf neq); apply neq_add_substC. *)
  (* Qed. *)

  (* Lemma subst_add c c' T D : *)
  (*   def (add c T D) -> subst_env c c' (add c T D) = add c' T D. *)
  (* Proof. *)
  (*   case: (boolP (c' == c))=>[/eqP->|]; first by rewrite subst_envK. *)
  (*   move=> neq H; case: D H=>//f; rewrite /add/dom; case: suppP => [v|]-H//_. *)
  (*   rewrite /upd/subst_env/look fnd_ins eq_refl /rem rem_ins eq_refl /add/dom/upd. *)
  (*    by rewrite supp_rem !inE neq /= rem_supp //; apply/notin_supp_fnd/eqP. *)
  (* Qed. *)

  (* Lemma def_addG k T D : def (add k T D) -> forall T', def (add k T' D). *)
  (* Proof. by move=> Df T'; apply: def_diff_value; apply: Df. Qed. *)

  (* Lemma def_subst_nested c c' D : def (subst_env c c' D) -> def D. *)
  (* Proof. by case: D. Qed. *)

  (* Lemma def_subst_dom c c' D : *)
  (*   def D -> *)
  (*   def (subst_env c c' D) = *)
  (*   (c \notin dom D) || ((c \in dom D) && (c' \notin (dom (rem c D)))). *)
  (* Proof. *)
  (*   case:D =>//f; rewrite /subst_env/look => _. *)
  (*   by case: (suppP c f)=>[v|]-H; rewrite H// def_addb andbC /=. *)
  (* Qed. *)

  (* Lemma binds_subst k k0 k1 v D : *)
  (*   def (subst_env k0 k1 D) -> *)
  (*   binds k v D -> *)
  (*   binds (if k == k0 then k1 else k) v (subst_env k0 k1 D). *)
  (* Proof. *)
  (*   case: (boolP (k0 == k1))=>[/eqP->|neq]; *)
  (*     first by case: ifP=>[/eqP->|]=>//; rewrite subst_envK. *)
  (*   case: D=>// f; rewrite /binds/subst_env/look/rem/add/upd/dom supp_rem !inE. *)
  (*   rewrite eq_sym neq /=. *)
  (*   case: (suppP k0 f)=>[v0|] E0; rewrite E0=>//. *)
  (*   + case: suppP => [v1|]-E1 // _ . *)
  (*     case: ifP=> [/eqP->|neq1]; first by rewrite fnd_ins eq_refl -E0. *)
  (*     rewrite fnd_ins; case: ifP=>[/eqP->|]; first by rewrite E1. *)
  (*     by rewrite fnd_rem neq1. *)
  (*   + by move=> _; case: ifP=>[/eqP->|]; first by rewrite E0. *)
  (* Qed. *)

  (* Lemma def_subst c c' D : *)
  (*   c' != c -> def D -> def (subst_env c c' D) -> *)
  (*   (c \notin dom D) || ((c \in dom D) && (c' \notin dom D)). *)
  (* Proof. by move=>eq Df; rewrite def_subst_dom // in_dom_rem // eq negb_and. Qed. *)

  (* Lemma def_next k T D : def D -> k \notin dom D -> def (add k T D). *)
  (* Proof. by rewrite def_addb=>->->. Qed. *)

  (* Lemma look_subst x c c' D : *)
  (*   def (subst_env c c' D) -> *)
  (*   look x (subst_env c c' D) = if c \in dom D then if x == c' then look c D *)
  (*                                                   else look x (rem c D) *)
  (*                               else look x D. *)
  (* Proof. *)
  (*   case: D =>//f; rewrite /subst_env/look/rem. *)
  (*   case: (suppP c f) => [v|] H; rewrite H // fnd_rem. *)
  (*   rewrite /add/rem/dom supp_rem !inE andbC. *)
  (*   case: suppP =>[v'|] H'/=. *)
  (*   - case: ifP=>///(rwP negPf); rewrite negbK=>/eqP-> _. *)
  (*     by rewrite fnd_ins fnd_rem; case: ifP=>//->. *)
  (*   - by rewrite fnd_ins fnd_rem. *)
  (* Qed. *)

  (* Lemma look_union x D1 D2 : look x (D1 \:/ D2) = if def (D1 \:/ D2) *)
  (*                                                 then if x \in dom D2 *)
  (*                                                      then look x D2 *)
  (*                                                      else look x D1 *)
  (*                                                 else None. *)
  (* Proof. *)
  (*   rewrite /look /union; case: D1=>// f1; case: D2=>//f2; case: ifP=>///=_. *)
  (*   by rewrite fnd_fcat. *)
  (* Qed. *)

End Env.

(* some representation independent lemmas for environments *)
Module Lemata (En : ENTRY) (Env : ENV En).
  Canonical env_eqMixin := EqMixin Env.eq_envP.
  Canonical env_eqType := Eval hnf in EqType Env.env Env.env_eqMixin.

  Import Env.

  Lemma env_eq_look' k D D':
    def D -> D == D' -> look k D == look k D'.
  Proof.
    by move=>Hdef/eqP=>->.
  Qed.

  Lemma env_eq_look k D D':
    def D -> D == D' -> look k D = look k D'.
  Proof.
    by move=>Hdef/eqP=>->.
  Qed.

  Lemma env_eq_def (D D' : env_eqType):
    def D -> D == D' -> def D'.
  Proof.
    move=>Hdef.
    rewrite eq_sym.
    by move/eqP=>->.
  Qed.

  Lemma eq_hd k t t' (D D' : env_eqType):
    def (Env.add k t D) -> add k t D == add k t' D' -> t = t'.
  Proof.
    move=>Hdef Heq.
    have Hdef':= env_eq_def Hdef Heq. (* this is not as pretty as it should be *)
    move:Heq.
    move/env_eq_look.
    move=>/(_ k Hdef).
    by (repeat rewrite look_add) ; first congruence ; try easy.
  Qed.

  Theorem add_in_dom x t E: def(add x t E) <-> x \in dom (add x t E).
  Proof.
    split.
    {
      move=>H.
      rewrite dom_add.
      - pose (x\in (pred1 x)).
        rewrite/in_mem;simpl.
        by apply: predU1l.
      - easy.
    }
    by apply in_dom_def.
  Qed.


  (* this lemma is a bit silly, not just a bit *)
  Lemma eq_rem k D D' :
    D = D' -> rem k D = rem k D'.
  Proof. by move=>->. Qed.

  Lemma eq_add k t D D' :
    def (add k t D) ->
    add k t D = add k t D' -> D = D'.
  Proof.
    move=> Def Eq; have Def':def (add k t D') by rewrite -Eq.
    move: Eq => /(eq_rem k); rewrite -!rem_add_id //.
  Qed.

  Theorem UniquenessBind a T T' D:
    binds a T D -> binds a T' D -> T = T'.
  Proof.
    rewrite/binds.
    move/eqP=>->/eqP.
    congruence.
  Qed.

  Lemma binds_top_addE a T T' D:
    def (add a T D) ->
    binds a T (add a T' D) ->
    T = T'.
  Proof.
    rewrite/binds.
    move/(def_diff_value T')=>H.
    rewrite look_add ; last by [].
    by move/eqP;case.
  Qed.

  Lemma def_addb : forall (k : En.K) (t : En.V) (E : env),
      def (add k t E) = def E && (k \notin dom E).
  Proof.
    move => k t E; move: (def_add k t E).
    case: (boolP (def (add k t E)))=>_.
    + by move=>/proj1/(_ is_true_true)=>[][->->].
    + move=>/proj2; case: (boolP (k \notin dom E))=>_; last by rewrite andbC.
        by case: (boolP (def E))=>// _ /(_ (conj is_true_true is_true_true)).
  Qed.

  (* convenience form of def_add *)
  Lemma def_add_assumption k T D:
    k \notin dom D -> def D -> def (add k T D).
  Proof.
    move=> H H'.
    by apply def_add.
  Qed.

    Lemma in_predU_r {T : eqType}(k : T) P Q : k \in Q -> k \in predU P Q.
    do 2! rewrite/(_\in_).
    rewrite/predU.
    simpl=>->.
    by rewrite Bool.orb_true_r.
  Qed.

  Lemma in_dom_add_diff k k' t E:
    k \in dom E -> def (add k' t E) -> k \in dom (add k' t E).
  Proof.
    move=>Hk Hdef.
    rewrite dom_add=>//.
    apply in_predU_r.
    by apply Hk.
  Qed.

  Lemma notin_predU {T : eqType}(k : T) P Q : k \notin P -> k \notin Q -> k \notin predU P Q.
  Proof.
    do !rewrite/(_\notin_)/predU/(_\in_) ; simpl.
    elim (P k)=>//.
  Qed.

  Lemma notin_dom_def k k' t E:
    k \notin dom E -> k != k' -> def (add k' t E) -> k \notin dom (add k' t E).
  Proof.
    move=> Hk Hkk' Hdef.
    rewrite dom_add ; last easy.
    by apply notin_predU; [rewrite/(_\notin_)/pred1=>// | apply Hk].
  Qed.

  Lemma notin_add_applied k k' T D:
    def (add k' T D) -> k \notin dom (add k' T D) -> (k != k') && (k \notin dom D).
  Proof. by move=>Hdef; rewrite notin_add. Qed.
End Lemata.
