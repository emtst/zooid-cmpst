From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import MPST.Atom.

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

  (* Parameter look_add a T D : def (add a T D) -> look a (add a T D) = Some T. *)

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
  Parameter env_eq_look' :
    forall (k : En.K) (D : env) (D' : env),
      def D -> D == D' -> look k D == look k D'.
  Parameter env_eq_look :
    forall (k : En.K) (D D': env),
      def D -> D == D' -> look k D = look k D'.
  Parameter env_eq_def :
    forall (D D': env), def D -> D == D' -> def D'.
  (* TODO this lemma (eq_hd) should also be a parameter, but somehow it fails *)
  (* Parameter eq_hd : *)
  (*   forall (k : En.K) (t t' : En.V) (D D' : env_eqType), *)
  (*     def (add k t D) -> add k t D == add k t' D' -> t = t'. *)
  Parameter singleton_def : forall (k : En.K) (v : En.V), def (add k v empty).
  Parameter in_dom_def : forall (a' : En.K) (D : env), a' \in dom D -> def D.
  Parameter dom_add :
    forall (k : En.K) (v : En.V) (E : env),
      def (add k v E) -> dom (add k v E) =i predU (pred1 k) (mem (dom E)).
  Parameter add_in_dom :
    forall (x : En.K) (t : En.V) (E : env), def (add x t E) <-> x \in dom (add x t E).
  Parameter rem_add_id :
    forall (k' : En.K) (v' : En.V) (D : env), def (add k' v' D) -> D = rem k' (add k' v' D).
  Parameter eq_rem : forall (k : En.K) (D D' : env), D = D' -> rem k D = rem k D'.
  Parameter eq_add :
    forall (k : En.K) (t : En.V) (D D' : env), def (add k t D) -> add k t D = add k t D' -> D = D'.
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

  (* update if present *)
  Definition upd x t (E : env) :=
    map (fun en => if x == fst en then (x, t) else en) E.

  (* update or insert *)
  Definition add_upd x t (E : env) :=
    if x \in (map fst E) then upd x t E else (x , t) :: E.

  Fixpoint look x (E : env) : option En.V :=
    match E with
    | nil => None
    | (x', t) :: E => if x == x' then Some t else look x E
    end
    .

  Definition add x t E := add_upd x t E.

  Definition rem x (E : env) := filter (fun en => x != fst en) E.

  Definition dom (E : env) := if def E then map fst E else [::].

  Definition dom_pred (E : env) : pred En.K := mem (dom E).

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

  (* Properties of defined environments *)
  Lemma look_add a T D: def (add a T D) -> look a (add a T D) = Some T.
  Admitted.

  Lemma look_add_deep a a' T D: a != a' -> def (add a T D) -> look a' (add a T D) == look a' D.
  Admitted.

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
  Check env_eq_def.

  Lemma eq_hd k t t' (D D' : env_eqType):
    def (add k t D) -> add k t D == add k t' D' -> t = t'.
  (* Proof. *)
  (*   move=>Hdef Heq. *)
  (*   have Hdef':= env_eq_def Hdef Heq. (* this is not as pretty as it should be *) *)
  (*   move:Heq. *)
  (*   move/env_eq_look. *)
  (*   move=>Hs. *)
  (*   have HH := Hs k Hdef. *)
  (*   move:HH. *)
  (*   by (repeat rewrite look_add) ; first congruence ; try easy. *)
  (* Qed. *)
  Admitted. (* this proof does not depend on the inductive D so it should be factorable *)

  Lemma singleton_def k v : def (add k v nil).
  Proof.
    by rewrite/def/add.
  Qed.

  Lemma in_dom_def a' D: a' \in dom D -> def D.
  Proof.
    unfold dom.
    case (def D)=>//.
  Qed.

  Lemma dom_add k v (E : env) : def (add k v E) ->
                                dom (add k v E) =i predU (pred1 k) (mem (dom E)).
  Admitted.

  (* this proof may be missing the point, it should be simpler *)
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

  Lemma rem_add_id k' v' D : def (add k' v' D) -> D = rem k' (add k' v' D).
  Admitted.

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

  (* TODO: continue importing lemmas from OldEnv.v from CONTINUE HERE and on *)
End Env.
