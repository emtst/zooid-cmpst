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
(*L to D and F: rem_add_idd is not true, see also later for environments as sequences*)
(*  Parameter rem_add_id :
    forall (k' : En.K) (v' : En.V) (D : env), def (add k' v' D) -> D = rem k' (add k' v' D).*)
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


  (*Definition eq_env : env -> env -> bool. Admitted.*)
  Definition eq_env (E E': env) : bool :=  E == E'.
  Definition eq_envP : Equality.axiom eq_env.
  Proof. move=> E E'; apply (eqP). Qed.

  Canonical env_eqMixin := EqMixin eq_envP.
  Canonical env_eqType := Eval hnf in EqType env env_eqMixin.

  Definition empty : env := [::].
  Definition def (E : env) := uniq (map fst E).
  Definition undef E := negb(def E).


  Lemma def_nil: def [::].
  Proof. by []. Qed.

  Lemma def_cons_def x t (E: env): def ((x,t) :: E) -> def E.
  Proof. unfold def. rewrite map_cons. rewrite cons_uniq. 
    move=> /andP[notin unique]. by apply: unique.
  Qed.

  Definition dom (E : env)  : seq En.K := if def E then map fst E else [::].

  Definition dom_pred (E : env) : pred En.K := mem (dom E).

  (*Lemma not_in_dom_nil x: x =*)


  Lemma dom_cons k v (E : env): def ((k,v)::E) -> dom ((k,v)::E) = k::(dom E).
  Proof.
  unfold dom; case: ifP; rewrite //=.
  move=> defcons ttt. case: ifP; rewrite //=.
  move=> nottrue. move: (def_cons_def defcons). by rewrite nottrue //=.
  Qed.

  Lemma in_dom_cons x T (E : env) : def ((x,T)::E) -> x \in dom ((x,T)::E).
  Proof. 
  unfold dom. case (@idP (def ((x,T)::E))); [simpl; intro; intro; apply mem_head | rewrite //].
  Qed.


  (* update if present *)
  Definition upd x t (E : env) :=
    map (fun en => if x == fst en then (x, t) else en) E.



  Lemma evennondef_upd_same_dom x T E: map fst (upd x T E) = map fst E .
  Proof. unfold upd. elim E; [by []| elim; move=> x0 T0 E0 hp; simpl; case: eqP; rewrite <-hp].
  + by move=> hp_eq; rewrite hp_eq //.
  + by rewrite //.
  Qed.

  Lemma upd_cons_head x t t0 (E0 : env): upd x t ((x,t0)::E0) = (x,t) :: (upd x t E0).
  Proof.
  unfold upd. rewrite map_cons. by case (@idP (x == (x, t0).1)); rewrite //. 
  Qed.

  Lemma upd_cons_nothead x t x0 t0 (E0 : env): 
    x != x0 -> upd x t ((x0,t0)::E0) = (x0,t0) :: (upd x t E0).
  Proof.
  unfold upd. rewrite map_cons. by case: ifP; rewrite //=. 
  Qed.


  (* update or insert *)
  Definition add_upd x t (E : env) : env:=
    if x \in dom E then upd x t E else (x , t) :: E.

  (*Lemma add_upd_nil x T: add_upd x T [::] = [:: (x,T)].
  Proof.
  unfold add_upd; by rewrite //.
  Qed.*)



  Fixpoint look x (E : env) : option En.V :=
    if def E then
      match E with
      | nil => None
      | (x', t) :: E => if x == x' then Some t else look x E
      end
    else None
    .

  Lemma look_cons x x' t E: def ((x', t) :: E) ->
    look x ((x', t) :: E) = (if x == x' then Some t else look x E).
  Proof. simpl; case (def ((x', t) :: E)); [rewrite // | by []]. Qed.


  Definition add x t (E : env) : env := add_upd x t E.
(*L to D and F: don't you want an add without update?*)

  Definition rem x (E : env) : env := filter (fun en => x != fst en) E.

  Lemma not_in_dom_nil x : x \notin dom [::].
  Proof. by []. Qed.

  Lemma in_dom_cons_eq x y t E : def ((y,t) :: E) -> 
    ( (x \in dom ((y,t) :: E)) = ((x == y) || (x \in dom E)) ).
  Proof.
  unfold dom. rewrite //.  move=> defcons. rewrite defcons. rewrite map_cons.
  have defE: def E. apply: def_cons_def. by apply: defcons.
  rewrite defE. by [].
  Qed.

  Lemma notin_dom_cons_eq x y t E : def ((y,t) :: E) -> 
    ( (x \notin dom ((y,t) :: E)) = (~~(x == y) && (x \notin dom E)) ).
  Proof.
  intro defE. rewrite <-negb_or. rewrite (in_dom_cons_eq); by[].
  Qed.

  Lemma notin_dom_cons_head x y t E : def ((y,t) :: E) -> 
    (x \notin dom ((y,t) :: E)) -> (x != y).
  Proof.
    move=> defcons notin.
    have nconj: (x != y) /\ (x \notin dom E).
      rewrite (rwP andP); rewrite <-(notin_dom_cons_eq _ defcons); by apply notin.
    by apply (proj1 nconj).
  Qed.

  Lemma notin_dom_cons_tail x y t E : def ((y,t) :: E) -> 
    (x \notin dom ((y,t) :: E)) -> (x \notin dom E).
  Proof.
    move=> defcons notin.
    have nconj: ~ (x == y) /\ (x \notin dom E).
      rewrite (rwP negP); rewrite (rwP andP); rewrite <-(notin_dom_cons_eq _ defcons); by apply notin.
    by apply (proj2 nconj).
  Qed.


  Lemma def_cons_not_head x y t E : def ((y,t) :: E) -> x \in dom E -> 
    x != y.
  Proof.
  move=> defcons. unfold dom. rewrite (def_cons_def defcons). move: defcons.
  unfold def. rewrite map_cons. rewrite cons_uniq. simpl. case (@idP (x==y)); [ | by []].
  move=>/eqP->. rewrite <-(rwP andP); elim.  congruence.
  Qed.



  Lemma notin_dom_upd_id x t (E : env) : def E -> x \notin dom E -> upd x t E = E.
  Proof.
    elim: E; [ by [] | elim].
    move=> x0 t0 E0 ih defcons. rewrite (notin_dom_cons_eq _ defcons). move=>/andP.
    elim; move=> diff notin. rewrite (upd_cons_nothead _ _ _ diff).
    rewrite (ih (def_cons_def defcons) notin); by [].
  Qed.

(*this last lemma and some of the above can be proven without the environment being defined...
is it worth to keep track of this second/stronger version?*)

(*L to D and F: here I had to add an hypothesis, namely def E*)
  Lemma in_domP x E : def E -> reflect (exists v, look x E = Some v) (x \in dom E).
  Proof. 
  elim E. 
    move => defnil; apply (iffP idP); [by [] | elim; by [] ].
  elim. move => x0 t0 E0 ih defcons.
  apply (iffP idP). rewrite in_dom_cons_eq; [ | by apply: defcons]. rewrite (look_cons _ defcons).
    case: (x==x0); [intro; exists t0; by [] | simpl; by apply: ih (def_cons_def defcons)].
  rewrite (look_cons _ defcons) in_dom_cons_eq; [ | by apply: defcons].
  case: (x==x0); [ by [] | simpl; case: (ih (def_cons_def defcons)); by []].
  Qed.


  (***************************************************************************************)


  Lemma look_not_some x D : ~ (exists v, look x D = Some v) -> look x D = None.
  Proof. elim look; [ intro; elim; exists a; by [] | by [] ]. Qed.

  Inductive look_spec x D : bool -> Prop :=
  | look_some v : look x D = Some v -> look_spec x D true
  | look_none : look x D = None -> look_spec x D false.

(*L to D and F: added hp def E  (in_domP legacy) *)
  Lemma domP x D : def D -> look_spec x D (x \in dom D).
  Proof.
    intro defD. case: (in_domP _ defD) =>[|/look_not_some].
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
  Lemma def_cons_notin_dom x T D: def ( (x, T) :: D) -> (x \notin dom D).
  Proof. unfold dom. case (def D); [| by []].
    unfold def; simpl. elim andP; [ elim; by [] | intro; by [] ]. 
  Qed.


  Lemma notin_dom_def_cons x T D: def D -> (x \notin dom D) -> def ((x,T)::D).
  Proof. 
  unfold dom. case (@idP (def D)); [ | by [] ]. 
  unfold def. rewrite map_cons. rewrite cons_uniq. intro unique. intro. intro notin.
  apply /andP. split; [by apply notin | by apply unique].
  Qed.

  Lemma not_indom_upd_id x T (D : env): def D -> x \notin dom D -> upd x T D = D.
  Proof.
  elim D; [unfold upd; by [] | elim].
  (*case: (@eqP def D).
  unfold dom. case: ifP; [ | by [] ]. elim D; [by [] | elim].*)
  move=> x0 T0 E0 ih defcons. rewrite notin_dom_cons_eq; [| by apply defcons]. 
  move=>/andP. elim. move=>/negP. move=> neq notin. rewrite upd_cons_nothead;
  [ rewrite (ih (def_cons_def defcons) notin); by []
  | rewrite <-(rwP negP) ; by []
  ].
  Qed.


  Lemma add_upd_head x T T' D: 
    def ((x,T) :: D) -> add_upd x T' ((x,T) :: D) = (x, T') :: D.
  Proof.
  unfold add_upd; move=> defcons. move: (in_dom_cons defcons). case: ifP; rewrite //=.
  move=> indom ttt. rewrite eq_refl.
  by rewrite 
    (notin_dom_upd_id _ (def_cons_def defcons) (def_cons_notin_dom defcons)) //=.
  Qed.



  Lemma def_iff_def_upd a T D: def D <-> def (upd a T D).
  Proof.
    unfold def; rewrite evennondef_upd_same_dom; by [].
  Qed.

  Lemma def_iff_def_updb a T D: def D = def (upd a T D).
  Proof.
    unfold def; rewrite evennondef_upd_same_dom; by [].
  Qed.

  Lemma in_dom_add_upd_same_dom x T E: x \in dom E -> dom (add_upd x T E) = dom E .
  Proof.
    intro. unfold add_upd, dom. rewrite H. rewrite <-def_iff_def_updb. rewrite (in_dom_def H).
    by apply: evennondef_upd_same_dom.
  Qed.

  Lemma in_dom_add_same_dom x T E: x \in dom E -> dom (add x T E) = dom E .
  Proof.
  unfold add. by apply in_dom_add_upd_same_dom.
  Qed.

  Lemma def_def_add_upd a T D: def D -> def (add_upd a T D).
  Proof. unfold add_upd. case: (@idP (a \in dom D)).
  + intro indom. unfold def. rewrite evennondef_upd_same_dom. by [].
  + unfold dom. intro H0. intro H1. move: H0. case: (@idP (def D)); [ |intro H; contradict H; apply H1].
    unfold def. rewrite map_cons. rewrite cons_uniq. intro unique. intro notin. apply /andP. 
    split; [simpl; apply /negP; by apply: notin | by apply: unique ].
  Qed.

  Lemma def_add_upd_def a T D: def (add_upd a T D) -> def D.
  Proof. unfold add_upd. by case: (a \in dom D); 
    [ move=> defu; rewrite def_iff_def_upd; apply defu | apply: def_cons_def].
  Qed.


  Lemma def_add_upd_def_eq a T D: def (add_upd a T D) <-> def D.
  Proof.
  split; [by apply: def_add_upd_def| by apply: def_def_add_upd].
  Qed.

  Lemma def_def_add a T D: def D -> def (add a T D).
  Proof. 
  unfold add; by apply def_def_add_upd.
  Qed.

  Lemma def_add_def a T D: def (add a T D) -> def D.
  Proof.
  unfold add; by apply def_add_upd_def.
  Qed.


  Lemma def_add_def_eq a T D: def (add a T D) <-> def D.
  Proof.
  split; [by apply: def_add_def| by apply: def_def_add].
  Qed.





(*   Lemma stupid0 (x y: En.K): (x == y) <-> (x = y).
  Proof. apply conj. apply /eqP. case eqP. by []. by[]. Qed.


  Lemma stupid (x: En.K) y: ~ (x == y) -> ~ (x = y).
  Proof. case eqP; rewrite //. Qed.
 *)


About negP.
  Locate "_ <> _".
  Locate "_ != _".
  Locate " ~ _". 


  SearchAbout eqb.

  Lemma look_add a T D: def (add a T D) -> look a (add a T D) = Some T.
  Proof.
  elim D; [intro; unfold add, add_upd; simpl; rewrite eq_refl // | ].
  elim. move=> x0 T0 E0; unfold add; move=> ih defadd.
  case (@idP (a \in dom ((x0, T0) :: E0))).
    + intro indom. unfold add_upd. rewrite indom. case (@idP (a==x0)); intro case_a.
      * rewrite (eqP case_a). rewrite upd_cons_head. rewrite look_cons. 
          by case (@idP (x0==x0)); rewrite //.
        move: defadd. unfold add_upd. 
          rewrite indom; rewrite (eqP case_a); rewrite upd_cons_head; by [].
      * have ainE0: a \in dom E0. move: indom. rewrite in_dom_cons_eq. 
          rewrite <-(rwP orP). by elim; [move: case_a; rewrite // | rewrite // ].
          by apply: (def_add_upd_def defadd).
        rewrite upd_cons_nothead; [| rewrite <-(rwP negP); by apply case_a ]. rewrite look_cons. 
          case (@idP (a==x0)); [intro H; contradict H; apply case_a | intro h; move: ih; elim].
          unfold add_upd. by case (@idP (a \in dom E0)); [rewrite // | move: ainE0; rewrite //].
          apply def_def_add_upd. by apply: (def_cons_def (in_dom_def indom)).
          move: defadd. unfold add_upd. 
            case: (@idP (a \in dom ((x0, T0) :: E0))); [ | intro H; contradict H; apply indom].
            rewrite upd_cons_nothead; [ by [] | ]. rewrite <-(rwP negP). by apply case_a.
    + unfold add_upd. case (@idP (a \in dom ((x0, T0) :: E0))); rewrite //. intro notindom. intro.
      rewrite look_cons.
      * by case (@idP (a==a)); rewrite //.
      * apply notin_dom_def_cons; 
        [ by apply: (def_add_upd_def defadd) 
        | by apply /negP; apply notindom
        ].
  Qed.


  Lemma look_add_deep a a' T D: a != a' -> def (add a T D) -> look a' (add a T D) == look a' D.
  Proof.
  elim D; [rewrite <-(rwP negP); rewrite eq_sym; simpl; case: ifP; rewrite // | elim].
  move=> x0 T0 E0. unfold add. move=> ih neq defadd.
  have defcons: def ((x0,T0):: E0). apply (def_add_upd_def defadd).
  move: ih defadd.
  unfold add_upd. case: ifP.
  + move=> inE0 ih. rewrite (in_dom_cons_eq _ defcons). rewrite inE0. rewrite orbT. 
    rewrite upd_cons_nothead. move=> defupd.
    rewrite (look_cons _ defupd). rewrite (look_cons _ defcons). case: ifP; [ by [] | ].
    move=> neq2. by rewrite (ih neq (def_cons_def defupd)) //.
    by apply (def_cons_not_head defcons inE0).
  + case (@idP (a==x0)).
    * move=>/eqP-eqax0; rewrite eqax0. rewrite (in_dom_cons defcons).
      move=> ninE0 ih. rewrite upd_cons_head. rewrite not_indom_upd_id.
      move: neq. rewrite <-(rwP negP); rewrite eq_sym. rewrite eqax0. move=> neq defT.
      rewrite (look_cons _ defT). rewrite (look_cons _ defcons). 
      move: neq; case: ifP; [rewrite (rwP negP); simpl; by [] | by []].
      by apply (def_cons_def defcons).
      by rewrite ninE0 //.
    * case: (@ifP _ (a \in dom ((x0, T0) :: E0))).
      rewrite (in_dom_cons_eq _ defcons). move=> or false1 false2. move: or false1. 
      rewrite false2. rewrite orbF. by congruence.
      move=> ndomcons neqax0 ndom ih defall.
      rewrite (look_cons _ defall). rewrite (look_cons _ defcons).
      case: ifP; [ move: neq; rewrite <-(rwP negP); rewrite eq_sym; by [] 
      | move=> neq2; case: ifP; by []]. 
  Qed.



  Lemma dom_add k v (E : env) : def (add k v E) ->
                                dom (add k v E) =i predU (pred1 k) (mem (dom E)).
  Proof.
  unfold pred_of_simpl, predU, pred1. simpl.
  move=> defadd. unfold eq_mem. unfold add, add_upd. move=> x.
  rewrite inE. case: ifP. 
  + unfold dom; rewrite <-def_iff_def_updb; rewrite (def_add_def defadd).
    rewrite evennondef_upd_same_dom. move=> kin. case: eqP; rewrite //; move=>->; apply kin.
  + move=> neq. apply in_dom_cons_eq. move: defadd. unfold add, add_upd; rewrite neq; by[].
  Qed.

  Lemma rem_head k v D: rem k ((k, v) :: D) = rem k D.
  Proof.
  unfold rem. rewrite //=. by case: ifP; move=>/eqP; rewrite //=.
  Qed.

  Lemma rem_nothead_comm k' k v D: k' != k ->
    rem k' ((k, v) :: D) = (k, v) :: rem k' D.
  Proof.
  unfold rem. simpl. by case eqP; rewrite //.
  Qed.

  Lemma notin_rem_id k' D: def D -> k' \notin dom D -> rem k' D = D.
  Proof.
  elim D; [rewrite // | elim]. 
  move=> k v E ih defcons notin.
  rewrite (rem_nothead_comm  ).
  * by rewrite (ih (def_cons_def defcons) (notin_dom_cons_tail defcons notin)) //.
  * by apply (notin_dom_cons_head defcons notin).
  Qed.


  Lemma rem_cons_id k v D : def ((k, v) :: D) -> rem k ((k,v) :: D) = D.
  Proof.
  unfold rem; simpl. case: eqP; rewrite //=. move=> triv defcons.
  move: (@notin_rem_id k D (def_cons_def defcons) (def_cons_notin_dom defcons)). by [].
  Qed.


  Lemma def_def_rem k D : def D -> def (rem k D).
  Proof.
  by apply subseq_uniq, map_subseq, filter_subseq. 
  Qed.


  Lemma filter_pr_subseq E1 E2 a: subseq (E1 : env) E2
    -> subseq (filter a E1) (filter a E2).
  Proof.
  elim: E2 E1; [ rewrite //=; move=> E1 /eqP->; by [] | ]. 
  move=> e0 E0 ih E1. elim E1; [ rewrite //=; by rewrite sub0seq //= | ].
  move=> e' E' ih'. rewrite //=. case: ifP.
  + move=>/eqP-eqe. rewrite eqe. move=> sub. case: ifP; rewrite //=.
    * case: ifP; [move=> triv holds; by apply ih, sub | rewrite eq_refl //=].
    * move=> doesnt; by apply ih, sub.
  + move=>/eqP-neqe sub. 
    apply (@subseq_trans _ [seq x <- E0 | a x]).
    * move: (ih _ sub). by [].
    * case: ifP; [move=> holds; by apply subseq_cons| by rewrite //=].
  Qed.



  Lemma def_rem_cons k' k v D : def (rem k' ((k,v)::D)) -> def (rem k' D).
  Proof.
  unfold def, rem. by apply subseq_uniq, map_subseq, 
    filter_pr_subseq, subseq_cons.
  Qed.

  Lemma indom_rem_indom k k' D: def D 
    -> k \in dom (rem k' D) -> k \in dom D.
  Proof.
  move=>defD. unfold dom. rewrite def_def_rem //=. rewrite defD //=.
  apply mem_subseq, map_subseq, filter_subseq. 
  Qed.

  Lemma dom_rem_rw k' D: def (rem k' D) -> 
    dom (rem k' D) = filter (fun x => k' != x) (map fst (rem k' D)).
  Proof.
  elim D; [ by rewrite //= | elim ]. move=> k0 v0 D0 ih.
  case (@idP (k0==k')). 
  + move=>/eqP->. move=> defrem. rewrite //=. 
    case: ifP; [rewrite <-(rwP negP); rewrite <-(rwP eqP); by [] |].
    move=> triv. by apply (ih (def_rem_cons defrem)).
  + move=>/negP-diff defrem. rewrite //=.
    case: ifP; [ rewrite //=
      | move=> falserw; move: diff; rewrite eq_sym; rewrite falserw; by []].
    case: ifP; rewrite //=. 
    rewrite dom_cons; [ 
      | move: defrem; rewrite //=; case: ifP; move=> falserw;
        move: diff; rewrite eq_sym; rewrite falserw; by []].
    rewrite (ih (def_rem_cons defrem)) //=.
  Qed.

  Lemma notin_dom_rem k k' D: def D 
    -> k \notin dom D -> k \notin dom (rem k' D).
  Proof.
  move=> defD. rewrite (dom_rem_rw (def_def_rem _ defD)). unfold dom.
  move:defD. case: ifP; rewrite //=. elim D; rewrite //=. elim; rewrite //=.
  move=> k0 v0 D0 ih defcons ttt notincons.
  case: ifP; rewrite //=.
  + case: ifP; rewrite //=. move=> diff ttt2.
    move: notincons. rewrite! in_cons. rewrite! negb_or.
   rewrite <-(rwP andP). elim; move=> diff2 knotin.
    apply /andP; apply conj; [by apply diff2
    | by apply (ih (def_cons_def defcons) ttt knotin)]. 
  + move=> weirdeq. have eqk: k0 = k'. 
     apply /eqP; rewrite eq_sym; by apply (negbFE weirdeq).
    apply (ih (def_cons_def defcons) ttt).
    move: notincons. rewrite in_cons.
    rewrite negb_or; rewrite <-(rwP andP); elim; by rewrite //=.
  Qed.




  Lemma dom_rem_eq k' D: k' \notin dom (rem k' D).
  Proof.
  case (@idP (def (rem k' D))); unfold dom; case: ifP; rewrite //=.
  elim D; rewrite //=. elim. rewrite //=. move=> k0 v0 D0 ih.
  case: ifP; [| move=> triv def0 ttt; by apply (ih def0 ttt)].
  move=> diff defcons ttt. rewrite //=. rewrite in_cons. 
  rewrite negb_or. apply /andP; apply (conj diff).
  by apply (ih (def_cons_def defcons) ttt).
  Qed.


  Lemma indom_diff_indom_rem k k' D: def D -> k != k'
    -> k \in dom D -> k \in dom (rem k' D).
  Proof.
  move=> defD. rewrite dom_rem_rw; [ | by apply (def_def_rem _ defD)].
  (*L to Everyone (Coq question): 
    why does the above not work with composing dom_rem_rw with def_def_rem ecc.?*)
  unfold dom. move=> diff. case: ifP; rewrite //=; elim.
  elim D; rewrite //=. elim. rewrite //=. move=> k0 v0 D0 ih incons.
  case: ifP; rewrite //=.
  + case: ifP; rewrite //=. move=> diff0. elim. move: incons.
    rewrite! in_cons //=. rewrite <-(rwP orP).
    elim; rewrite <-(rwP orP); [ by apply or_introl | move=> kin].
    apply or_intror. by apply (ih kin).
  + move=> weirdeq. have eqk: k0 = k'. 
     apply /eqP; rewrite eq_sym; by apply (negbFE weirdeq).
    move: incons. rewrite eqk. rewrite in_cons.
    rewrite <-(rwP orP); elim;
    [move=>/eqP-eqfalse; move: diff; rewrite eqfalse; rewrite <-(rwP negP); by []
    | apply ih].
  Qed.

(*def_cons_notin_dom*)

(*The lemma:

  Lemma rem_add_id k' v' D : def (add k' v' D) -> D = rem k' (add k' v' D).
  Proof.
  unfold add, add_upd. case: ifP.
  Qed.

is false. Uncomment and see the incomplete proof to get convinced. However the following versions are true.

L to L : two lemmas one with hp k' notin dom D and the other def (k', v) :: D, but they really are property of add. 
*)







  Lemma rem_upd k k' v D: rem k' (upd k v D) = upd k v (rem k' D).
  Proof.
  elim D; [ by [] | elim; move=> k0 v0 D0 ih].
  case (@idP (k0 == k')). 
  + move=>/eqP->. rewrite rem_head. case (@idP (k'==k)).
    - move=>/eqP-eqk. move: ih. rewrite eqk.
      rewrite upd_cons_head; rewrite rem_head. by [].
    - move=>/negP-diff. 
      rewrite upd_cons_nothead; [ | by rewrite eq_sym //=].
      rewrite rem_head. by rewrite //=.
  + move=>/negP-diff. rewrite rem_nothead_comm; 
    [ case (@idP (k'==k)) | rewrite eq_sym; by apply diff].
    - move=>/eqP-eqk. move: ih diff. rewrite eqk (@eq_sym _ k0). move=> ih diff.
      rewrite! (upd_cons_nothead _ _ _ diff)
        ; rewrite (rem_nothead_comm _ _ diff).
      rewrite ih; by [].
    - move=>/negP-diff2. case (@idP (k==k0)). 
      * move=>/eqP-eqk. move: ih. rewrite eqk. move=>ih. 
        rewrite! upd_cons_head. rewrite rem_nothead_comm;
          [ by rewrite ih //=| rewrite eq_sym; by apply diff].
      * move=>/negP-diff3. rewrite! (upd_cons_nothead _ _ _ diff3).
        rewrite rem_nothead_comm; [by rewrite ih //= 
          | rewrite eq_sym; by apply diff].
  Qed.

  Lemma rem_add k k' v D : def D -> k != k' -> 
    rem k' (add k v D) = add k v (rem k' D).
  Proof.
  unfold add, add_upd.
  case: ifP.
  + move=> indomD defD diff. 
    move: (indom_diff_indom_rem defD diff indomD).
    case: ifP; rewrite //=. by rewrite rem_upd //=.
  + move=> weird defD diff.
    have knotin: k \notin dom (rem k' D).
      by apply (notin_dom_rem _ defD (negbT weird)).
    move: knotin; rewrite <-(rwP negP).
    case: ifP; rewrite //=.
    move=> weird2 ttt. move: diff; rewrite eq_sym. 
    by case: ifP; rewrite //=.
  Qed.


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