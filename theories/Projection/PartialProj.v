From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.

From Paco Require Import paco paco1 paco2.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import MPST.Common.
Require Import MPST.Local.
Require Import MPST.Session.

Require Import MPST.Projection.IProject.

Fixpoint merge (A : eqType) (oL : A) (K : seq A) :=
  match K with
  | [::] => Some oL
  | h::t => if h == oL then merge oL t
            else None
  end.

Notation merge_all := (merge_all (@merge _)).

Fixpoint partial_proj (l : l_ty) (r : role) : option s_ty :=
  match l with
  | l_end => Some (s_end)
  | l_var v => Some (s_var v)
  | l_rec L =>
    match partial_proj L r with
    | Some s => Some (if s_binds 0 s then s_end else s_rec s)
    | _ => None
    end
    | l_msg a p Ks =>
      match (fix prj_all Ks r :=
               match Ks with
               | [::] => Some [::]
               | K::Ks =>
                 match partial_proj K.2.2 r, prj_all Ks r with
                 | Some s, Some Ks => Some ((K.1, (K.2.1, s)) :: Ks)
                 | _, _ => None
                 end
               end
            ) Ks r with
      | Some Ks => if p == r then Some (s_msg a Ks)
                   else merge_all [seq K.2.2 | K <- Ks]
      | None => None
      end
  end.

Fixpoint pprj_all (Ks : seq (lbl * (mty * l_ty))) (r : role)
  : option (seq (lbl * (mty * s_ty))) :=
  match Ks with
  | [::] => Some [::]
  | K::Ks => match partial_proj K.2.2 r, pprj_all Ks r with
             | Some s, Some Ks => Some ((K.1, (K.2.1, s)) :: Ks)
             | _, _ => None
             end
  end.

Lemma partialproj_all a p Ks r
  : partial_proj (l_msg a p Ks) r =
    match pprj_all Ks r with
    | Some Ks' => if p == r then Some (s_msg a Ks')
                  else merge_all [seq K.2.2 | K <- Ks']
    | None => None
    end.
Proof. by []. Qed.

Lemma merge_some (A : eqType)
      (K : lbl * (mty * A))
      (Ks : seq (lbl * (mty * A))) L
  : merge K.2.2 [seq K0.2.2 | K0 <- Ks] == Some L -> K.2.2 = L.
Proof. by elim: Ks=>[/eqP-[]//|K' Ks Ih/=]; case:ifP. Qed.

Notation lmerge_all := (IProject.merge_all simple_merge).

Lemma lmerge_some (K : lbl * (mty * l_ty)) (Ks : seq (lbl * (mty * l_ty))) L
  : simple_merge K.2.2 [seq K0.2.2 | K0 <- Ks] == Some L -> K.2.2 = L.
Proof. by elim: Ks=>[/eqP-[]//|K' Ks Ih/=]; case:ifP. Qed.

Lemma merge_pprj L' Ks L p S
  : simple_merge L' [seq K.2.2 | K <- Ks] == Some L ->
    partial_proj L p == Some S ->
    exists Ks', pprj_all Ks p = Some Ks' /\
                merge S [seq K.2.2 | K <- Ks'] = Some S.
Proof.
  elim: Ks=>[_|K' Ks Ih]/=; first (by exists [::]; split); move: Ih.
  case: ifP=>///eqP<- Ih M_L'; move: (lmerge_some M_L')=>-> /eqP-L_S.
  rewrite L_S; move: L_S=>/eqP-L_S; move: (Ih M_L' L_S) => [Ks' [Ksp M_S]].
  by exists ((K'.1, (K'.2.1, S)):: Ks'); rewrite Ksp /= eq_refl M_S.
Qed.

Lemma mergeall_pprj Ks L p S
  : lmerge_all [seq K.2.2 | K <- Ks] == Some L ->
    partial_proj L p == Some S ->
    exists Ks', pprj_all Ks p = Some Ks' /\
                merge_all [seq K.2.2 | K <- Ks'] = Some S.
Proof.
  case: Ks=>[//|K Ks]/=; move=> H; move: (lmerge_some H)=>KL.
  move: KL H=>-> H /eqP-L_S; rewrite L_S; move: L_S=>/eqP-L_S.
  move: (merge_pprj H L_S)=>[Ks' [Ksp M_S]].
  by exists ((K.1, (K.2.1, S)) :: Ks'); rewrite Ksp/= M_S.
Qed.

Lemma fun_mergeall (A B : eqType) (f : A -> B) (Ks : seq (lbl * (mty * A))) X
  : injective f ->
    merge_all [seq f x.2.2 | x <- Ks] == Some (f X) ->
    merge_all [seq x.2.2 | x <- Ks] == Some X.
Proof.
  case: Ks=>[//|K Ks/=] I; elim: Ks=>[|K' Ks]//=.
  - by move=>/eqP-[/I->].
  - by move=> Ih; case: ifP=>///eqP-[/I->]; rewrite eq_refl=>/Ih.
Qed.

Lemma mergeall_fun (A B : eqType) (f : A -> B) (Ks : seq (lbl * (mty * A))) X:
  merge_all [seq x.2.2 | x <- Ks] == Some X
  -> merge_all [seq f x.2.2 | x <- Ks] == Some (f X).
Proof.
  case: Ks=>[//|K Ks/=]; elim: Ks=>[|K' Ks]//=.
  - by move=>/eqP-[->].
  - by move=> Ih; case: ifP=>///eqP-[->]; rewrite eq_refl=>/Ih.
Qed.


Lemma pprjall_merge p Ks KsL L :
  pprj_all Ks p == Some KsL ->
  merge_all [seq K0.2.2 | K0 <- KsL] == Some L ->
  forall K, member K Ks -> partial_proj K.2.2 p == Some L.
Proof.
  case: KsL=>//= Kl KsL; case: Ks=>//= Kg Ks.
  case Kg_p: partial_proj => [Lp | //]; case Ks_p: pprj_all => [Ksp | //]/=.
  move=> Eq; move: Eq Ks_p => /eqP-[<-->] /eqP-Prj Mrg {Kl Ksp}.
  move:Mrg (merge_some Mrg)=>/=Mrg Eq; move: Eq Mrg Kg_p=>->Mrg /eqP-Kg_p.
  move=> K [<-//|]; move: Prj Mrg K {Lp Kg_p Kg}.
  elim: Ks KsL=>//= Kg Ks Ih KsL.
  case Kg_p: partial_proj => [Lp | //]; case Ks_p: pprj_all => [Ksp | //]/=.
  move=> Eq; move: Eq Ih Ks_p Kg_p=>/eqP-[<-]//= Ih /eqP-Prj.
  case: ifP=>[/eqP-> {Lp}|//] /eqP-Kg_p Mrg K [<-//|].
  by move: Prj=>/Ih/(_ Mrg K).
Qed.

Lemma pprjall_some p Ks Ks' :
  pprj_all Ks p == Some Ks' ->
  forall K,
    member K Ks ->
    exists L, member (K.1, (K.2.1, L)) Ks' /\ partial_proj K.2.2 p = Some L.
Proof.
  elim: Ks=>//= Kl Ks Ih in Ks' *.
  case Kl_p: partial_proj=>[s|//].
  case Ks_p: pprj_all=>[Ks0|//]; move: Ks_p=>/eqP/Ih-{Ih} Ih.
  move=>/eqP-[<-] K [E|/Ih-{Ih}[s' [M Kp]]]{Ks'}.
  - by move: E Kl_p=>-> {Kl}; exists s; split=>//; left.
  - by exists s'; split=>//; right.
Qed.
