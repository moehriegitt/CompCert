(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Constructions of semi-lattices. *)

Require Import Coqlib.
Require Import Maps.
Require Import FSets.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

(** * Signatures of semi-lattices *)

(** A semi-lattice is a type [t] equipped with an equivalence relation [eq],
  a boolean equivalence test [beq], a partial order [ge], a smallest element
  [bot], and an upper bound operation [lub].
  Note that we do not demand that [lub] computes the least upper bound. *)

Module Type SEMILATTICE.

  Parameter t: Type.
  Parameter eq: t -> t -> Prop.
  Axiom eq_refl: forall x, eq x x.
  Axiom eq_sym: forall x y, eq x y -> eq y x.
  Axiom eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Parameter beq: t -> t -> bool.
  Axiom beq_correct: forall x y, beq x y = true -> eq x y.
  Parameter ge: t -> t -> Prop.
  Axiom ge_refl: forall x y, eq x y -> ge x y.
  Axiom ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Parameter bot: t.
  Axiom ge_bot: forall x, ge x bot.
  Parameter lub: t -> t -> t.
  Axiom ge_lub_left: forall x y, ge (lub x y) x.
  Axiom ge_lub_right: forall x y, ge (lub x y) y.

End SEMILATTICE.

(** A semi-lattice ``with top'' is similar, but also has a greatest
  element [top]. *)

Module Type SEMILATTICE_WITH_TOP.

  Include SEMILATTICE.
  Parameter top: t.
  Axiom ge_top: forall x, ge top x.

End SEMILATTICE_WITH_TOP.

(** * Semi-lattice over maps *)

Set Implicit Arguments.

(** Given a semi-lattice (without top) [L], the following functor implements
  a semi-lattice structure over finite maps from positive numbers to [L.t].
  The default value for these maps is [L.bot].  Bottom elements are not smashed. *)

Module LPMap1(L: SEMILATTICE) <: SEMILATTICE.

Definition t := PTree.t L.t.

Definition get (p: positive) (x: t) : L.t :=
  match x!p with None => L.bot | Some x => x end.

Definition set (p: positive) (v: L.t) (x: t) : t :=
  if L.beq v L.bot
  then PTree.remove p x
  else PTree.set p v x.

Lemma gsspec:
  forall p v x q,
  L.eq (get q (set p v x)) (if peq q p then v else get q x).
Proof.
  intros. unfold set, get.
  destruct (L.beq v L.bot) eqn:EBOT.
  rewrite PTree.grspec. unfold PTree.elt_eq. destruct (peq q p).
  apply L.eq_sym. apply L.beq_correct; auto.
  apply L.eq_refl.
  rewrite PTree.gsspec. destruct (peq q p); apply L.eq_refl.
Qed.

Definition eq (x y: t) : Prop :=
  forall p, L.eq (get p x) (get p y).

Lemma eq_refl: forall x, eq x x.
Proof.
  unfold eq; intros. apply L.eq_refl.
Qed.

Lemma eq_sym: forall x y, eq x y -> eq y x.
Proof.
  unfold eq; intros. apply L.eq_sym; auto.
Qed.

Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
Proof.
  unfold eq; intros. eapply L.eq_trans; eauto.
Qed.

Definition beq (x y: t) : bool := PTree.beq L.beq x y.

Lemma beq_correct: forall x y, beq x y = true -> eq x y.
Proof.
  unfold beq; intros; red; intros. unfold get.
  rewrite PTree.beq_correct in H. specialize (H p).
  destruct (x!p); destruct (y!p); intuition.
  apply L.beq_correct; auto.
  apply L.eq_refl.
Qed.

Definition ge (x y: t) : Prop :=
  forall p, L.ge (get p x) (get p y).

Lemma ge_refl: forall x y, eq x y -> ge x y.
Proof.
  unfold ge, eq; intros. apply L.ge_refl. auto.
Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof.
  unfold ge; intros. apply L.ge_trans with (get p y); auto.
Qed.

Definition bot : t := PTree.empty _.

Lemma get_bot: forall p, get p bot = L.bot.
Proof.
 intros. unfold get, bot. rewrite PTree.gempty. auto.
Qed.

Lemma ge_bot: forall x, ge x bot.
Proof.
  unfold ge; intros. rewrite get_bot. apply L.ge_bot.
Qed.

(** A [combine] operation over the type [PTree.t L.t] that attempts
  to share its result with its arguments. *)

Section COMBINE.

Variable f: option L.t -> option L.t -> option L.t.
Hypothesis f_none_none: f None None = None.

Definition opt_eq (ox oy: option L.t) : Prop :=
  match ox, oy with
  | None, None => True
  | Some x, Some y => L.eq x y
  | _, _ => False
  end.

Lemma opt_eq_refl: forall ox, opt_eq ox ox.
Proof.
  intros. unfold opt_eq. destruct ox. apply L.eq_refl. auto.
Qed.

Lemma opt_eq_sym: forall ox oy, opt_eq ox oy -> opt_eq oy ox.
Proof.
  unfold opt_eq. destruct ox; destruct oy; auto. apply L.eq_sym.
Qed.

Lemma opt_eq_trans: forall ox oy oz, opt_eq ox oy -> opt_eq oy oz -> opt_eq ox oz.
Proof.
  unfold opt_eq. destruct ox; destruct oy; destruct oz; intuition.
  eapply L.eq_trans; eauto.
Qed.

Definition opt_beq (ox oy: option L.t) : bool :=
  match ox, oy with
  | None, None => true
  | Some x, Some y => L.beq x y
  | _, _ => false
  end.

Lemma opt_beq_correct:
  forall ox oy, opt_beq ox oy = true -> opt_eq ox oy.
Proof.
  unfold opt_beq, opt_eq. destruct ox; destruct oy; try congruence.
  intros. apply L.beq_correct; auto.
  auto.
Qed.

Definition tree_eq (m1 m2: PTree.t L.t) : Prop :=
  forall i, opt_eq (PTree.get i m1) (PTree.get i m2).

Lemma tree_eq_refl: forall m, tree_eq m m.
Proof. intros; red; intros; apply opt_eq_refl. Qed.

Lemma tree_eq_sym: forall m1 m2, tree_eq m1 m2 -> tree_eq m2 m1.
Proof. intros; red; intros; apply opt_eq_sym; auto. Qed.

Lemma tree_eq_trans: forall m1 m2 m3, tree_eq m1 m2 -> tree_eq m2 m3 -> tree_eq m1 m3.
Proof. intros; red; intros; apply opt_eq_trans with (PTree.get i m2); auto. Qed.

Lemma tree_eq_node:
  forall l1 o1 r1 l2 o2 r2,
  tree_eq l1 l2 -> tree_eq r1 r2 -> opt_eq o1 o2 ->
  tree_eq (PTree.Node l1 o1 r1) (PTree.Node l2 o2 r2).
Proof.
  intros; red; intros.
  destruct i.
 rewrite !PTree.get_xI_Node; auto.
 rewrite !PTree.get_xO_Node; auto.
 rewrite !PTree.get_xH_Node; auto.
Qed.

Hint Resolve opt_beq_correct opt_eq_refl opt_eq_sym
             tree_eq_refl tree_eq_sym
             tree_eq_node  : combine.

Lemma tree_eq_Nodes_not_Empty:
  forall m,  ~ tree_eq (PTree.Nodes m) PTree.Empty.
Proof.
unfold not, tree_eq.
induction m; intros.
-
apply IHm; clear IHm; intro i; specialize (H (xI i)).
rewrite PTree.gempty in *. apply H.
-
apply (H xH).
-
apply (H xH).
-
apply IHm; clear IHm; intro i; specialize (H (xO i)).
rewrite PTree.gempty in *. apply H.
-
apply IHm1; clear IHm1; intro i; specialize (H (xO i)).
rewrite PTree.gempty in *. apply H.
-
apply IHm; clear IHm; intro i; specialize (H (xO i)).
rewrite PTree.gempty in *. apply H.
-
apply (H xH).
Qed.

Inductive changed: Type := Unchanged | Chempty | Changed (m: PTree.tree' L.t).

Fixpoint combine_l (m : PTree.tree' L.t) {struct m} : changed :=
  match m with
  | PTree.Node001 r => match combine_l r with
                                      | Unchanged => Unchanged
                                      | Chempty => Chempty
                                      | Changed r' => Changed (PTree.Node001 r')
                                      end
  | PTree.Node010 o => match f (Some o) None with
                                       | None => Chempty
                                       | Some o' => if L.beq o' o then Unchanged else Changed (PTree.Node010 o')
                                       end
  | PTree.Node011 o r => match f (Some o) None, combine_l r with
                                         | None, Unchanged => Changed (PTree.Node001 r)
                                         | None, Chempty => Chempty
                                         | None, Changed r' => Changed (PTree.Node001 r')
                                         | Some o', Unchanged => if L.beq o' o then Unchanged else Changed (PTree.Node011 o' r)
                                         | Some o', Chempty => if L.beq o' o then Changed (PTree.Node010 o) else Changed (PTree.Node010 o')
                                         | Some o', Changed r' => if L.beq o' o then Changed (PTree.Node011 o r') else Changed (PTree.Node011 o' r')
                                         end
  | PTree.Node100 l => match combine_l l with
                                      | Unchanged => Unchanged
                                      | Chempty => Chempty
                                      | Changed l' => Changed (PTree.Node100 l')
                                      end
  | PTree.Node101 l r => match combine_l l, combine_l r with
                                      | Unchanged, Unchanged => Unchanged
                                      | Unchanged, Chempty => Changed (PTree.Node100 l)
                                      | Unchanged, Changed r' => Changed (PTree.Node101 l r')
                                      | Chempty, Unchanged => Changed (PTree.Node001 r)
                                      | Chempty, Chempty => Chempty
                                      | Chempty, Changed r' => Changed (PTree.Node001 r')
                                      | Changed l', Unchanged => Changed (PTree.Node101 l' r)
                                      | Changed l', Chempty => Changed (PTree.Node100 l')
                                      | Changed l', Changed r' => Changed (PTree.Node101 l' r')
                                      end
  | PTree.Node110 l o => match combine_l l, f (Some o) None with
                                         | Unchanged, None => Changed (PTree.Node100 l)
                                         | Unchanged, Some o' => if L.beq o' o then Unchanged else Changed (PTree.Node110 l o')
                                         | Chempty, None => Chempty
                                         | Chempty, Some o' => if L.beq o' o then Changed (PTree.Node010 o) else Changed (PTree.Node010 o')
                                         | Changed l', None => Changed (PTree.Node100 l')
                                         | Changed l', Some o' => if L.beq o' o then Changed (PTree.Node110 l' o) else Changed (PTree.Node110 l' o')
                                         end
  | PTree.Node111 l o r => match combine_l l, f (Some o) None, combine_l r with
                   | Unchanged, None, Unchanged => Changed (PTree.Node101 l r)
                   | Unchanged, None, Chempty => Changed (PTree.Node100 l)
                   | Unchanged, None, Changed r' => Changed (PTree.Node101 l r')
                   | Unchanged, Some o', Unchanged => if L.beq o' o then Changed (PTree.Node111 l o r) else Changed (PTree.Node111 l o' r)
                   | Unchanged, Some o', Chempty => if L.beq o' o then Changed (PTree.Node110 l o) else Changed (PTree.Node110 l o')
                   | Unchanged, Some o', Changed r' => if L.beq o' o then Changed (PTree.Node111 l o r') else Changed (PTree.Node111 l o' r')
                   | Chempty, None, Unchanged => Changed (PTree.Node001 r)
                   | Chempty, None, Chempty => Chempty
                   | Chempty, None, Changed r' => Changed (PTree.Node001 r')
                   | Chempty, Some o', Unchanged => if L.beq o' o then Changed (PTree.Node011 o r) else Changed (PTree.Node011 o' r)
                   | Chempty, Some o', Chempty => if L.beq o' o then Changed (PTree.Node010 o) else Changed (PTree.Node010 o')
                   | Chempty, Some o', Changed r' => if L.beq o' o then Changed (PTree.Node011 o r') else Changed (PTree.Node011 o' r')
                   | Changed l', None, Unchanged => Changed (PTree.Node101 l' r)
                   | Changed l', None, Chempty => Changed (PTree.Node100 l')
                   | Changed l', None, Changed r' => Changed (PTree.Node101 l' r')
                   | Changed l', Some o', Unchanged => if L.beq o' o then Changed (PTree.Node111 l' o r) else Changed (PTree.Node111 l' o' r)
                   | Changed l', Some o', Chempty =>  if L.beq o' o then Changed (PTree.Node110 l' o) else Changed (PTree.Node110 l' o')
                   | Changed l', Some o', Changed r' => if L.beq o' o then Changed (PTree.Node111 l' o r') else Changed (PTree.Node111 l' o' r')
                   end
 end.

Lemma combine_l_eq':
  forall m,
  tree_eq (match combine_l m with Unchanged => PTree.Nodes m | Chempty => PTree.Empty | Changed m' => PTree.Nodes m' end)
          (PTree.xcombine_l f (PTree.Nodes m)).
Proof.
  simpl.
  induction m; simpl;
  repeat match goal with 
  | H: tree_eq (PTree.Nodes _) PTree.Empty |- _ => 
           contradiction (tree_eq_Nodes_not_Empty H)
  | H: tree_eq PTree.Empty (PTree.Nodes _) |- _ => 
           apply tree_eq_sym in H; contradiction (tree_eq_Nodes_not_Empty H)
 | |- context [match match?A with _ => _ end with _ => _ end ] => destruct A eqn:?H
 | |- context [match ?A with _ => _ end] => destruct A eqn:?H
 | |- _ => simple apply tree_eq_refl
 end;
 intro i; destruct i; try apply opt_eq_refl;
 repeat match goal with H: tree_eq _ _ |- _ => apply (H i) || clear H end;
 apply L.eq_sym; apply L.beq_correct; auto.
Qed.

Lemma combine_l_eq:
  forall m x,
  combine_l m = x ->
  match x with
  | Unchanged => tree_eq (PTree.Nodes m) (PTree.xcombine_l f (PTree.Nodes m))
  | Chempty => tree_eq PTree.Empty (PTree.xcombine_l f (PTree.Nodes m))
  | Changed m' => tree_eq (PTree.Nodes m') (PTree.xcombine_l f (PTree.Nodes m))
  end.
Proof.
intros.
pose proof (combine_l_eq' m); rewrite H in H0; destruct x; auto.
Qed.

Fixpoint combine_r (m : PTree.tree' L.t) {struct m} : changed :=
  match m with
  | PTree.Node001 r => match combine_r r with
                                      | Unchanged => Unchanged
                                      | Chempty => Chempty
                                      | Changed r' => Changed (PTree.Node001 r')
                                      end
  | PTree.Node010 o => match f None (Some o) with
                                       | None => Chempty
                                       | Some o' => if L.beq o' o then Unchanged else Changed (PTree.Node010 o')
                                       end
  | PTree.Node011 o r => match f None (Some o), combine_r r with
                                         | None, Unchanged => Changed (PTree.Node001 r)
                                         | None, Chempty => Chempty
                                         | None, Changed r' => Changed (PTree.Node001 r')
                                         | Some o', Unchanged => if L.beq o' o then Unchanged else Changed (PTree.Node011 o' r)
                                         | Some o', Chempty => if L.beq o' o then Changed (PTree.Node010 o) else Changed (PTree.Node010 o')
                                         | Some o', Changed r' => if L.beq o' o then Changed (PTree.Node011 o r') else Changed (PTree.Node011 o' r')
                                         end
  | PTree.Node100 l => match combine_r l with
                                      | Unchanged => Unchanged
                                      | Chempty => Chempty
                                      | Changed l' => Changed (PTree.Node100 l')
                                      end
  | PTree.Node101 l r => match combine_r l, combine_r r with
                                      | Unchanged, Unchanged => Unchanged
                                      | Unchanged, Chempty => Changed (PTree.Node100 l)
                                      | Unchanged, Changed r' => Changed (PTree.Node101 l r')
                                      | Chempty, Unchanged => Changed (PTree.Node001 r)
                                      | Chempty, Chempty => Chempty
                                      | Chempty, Changed r' => Changed (PTree.Node001 r')
                                      | Changed l', Unchanged => Changed (PTree.Node101 l' r)
                                      | Changed l', Chempty => Changed (PTree.Node100 l')
                                      | Changed l', Changed r' => Changed (PTree.Node101 l' r')
                                      end
  | PTree.Node110 l o => match combine_r l, f None (Some o) with
                                         | Unchanged, None => Changed (PTree.Node100 l)
                                         | Unchanged, Some o' => if L.beq o' o then Unchanged else Changed (PTree.Node110 l o')
                                         | Chempty, None => Chempty
                                         | Chempty, Some o' => if L.beq o' o then Changed (PTree.Node010 o) else Changed (PTree.Node010 o')
                                         | Changed l', None => Changed (PTree.Node100 l')
                                         | Changed l', Some o' => if L.beq o' o then Changed (PTree.Node110 l' o) else Changed (PTree.Node110 l' o')
                                         end
  | PTree.Node111 l o r => match combine_r l, f None (Some o), combine_r r with
                   | Unchanged, None, Unchanged => Changed (PTree.Node101 l r)
                   | Unchanged, None, Chempty => Changed (PTree.Node100 l)
                   | Unchanged, None, Changed r' => Changed (PTree.Node101 l r')
                   | Unchanged, Some o', Unchanged => if L.beq o' o then Changed (PTree.Node111 l o r) else Changed (PTree.Node111 l o' r)
                   | Unchanged, Some o', Chempty => if L.beq o' o then Changed (PTree.Node110 l o) else Changed (PTree.Node110 l o')
                   | Unchanged, Some o', Changed r' => if L.beq o' o then Changed (PTree.Node111 l o r') else Changed (PTree.Node111 l o' r')
                   | Chempty, None, Unchanged => Changed (PTree.Node001 r)
                   | Chempty, None, Chempty => Chempty
                   | Chempty, None, Changed r' => Changed (PTree.Node001 r')
                   | Chempty, Some o', Unchanged => if L.beq o' o then Changed (PTree.Node011 o r) else Changed (PTree.Node011 o' r)
                   | Chempty, Some o', Chempty => if L.beq o' o then Changed (PTree.Node010 o) else Changed (PTree.Node010 o')
                   | Chempty, Some o', Changed r' => if L.beq o' o then Changed (PTree.Node011 o r') else Changed (PTree.Node011 o' r')
                   | Changed l', None, Unchanged => Changed (PTree.Node101 l' r)
                   | Changed l', None, Chempty => Changed (PTree.Node100 l')
                   | Changed l', None, Changed r' => Changed (PTree.Node101 l' r')
                   | Changed l', Some o', Unchanged => if L.beq o' o then Changed (PTree.Node111 l' o r) else Changed (PTree.Node111 l' o' r)
                   | Changed l', Some o', Chempty =>  if L.beq o' o then Changed (PTree.Node110 l' o) else Changed (PTree.Node110 l' o')
                   | Changed l', Some o', Changed r' => if L.beq o' o then Changed (PTree.Node111 l' o r') else Changed (PTree.Node111 l' o' r')
                   end
 end.

Lemma combine_r_eq':
  forall m,
  tree_eq (match combine_r m with Unchanged => PTree.Nodes m | Chempty => PTree.Empty | Changed m' => PTree.Nodes m' end)
          (PTree.xcombine_r f (PTree.Nodes m)).
Proof.
  simpl.
  induction m; simpl;
  repeat match goal with 
  | H: tree_eq (PTree.Nodes _) PTree.Empty |- _ => 
           contradiction (tree_eq_Nodes_not_Empty H)
  | H: tree_eq PTree.Empty (PTree.Nodes _) |- _ => 
           apply tree_eq_sym in H; contradiction (tree_eq_Nodes_not_Empty H)
 | |- context [match match?A with _ => _ end with _ => _ end ] => destruct A eqn:?H
 | |- context [match ?A with _ => _ end] => destruct A eqn:?H
 | |- _ => simple apply tree_eq_refl
 end;
 intro i; destruct i; try apply opt_eq_refl;
 repeat match goal with H: tree_eq _ _ |- _ => apply (H i) || clear H end;
 apply L.eq_sym; apply L.beq_correct; auto.
Qed.

Lemma combine_r_eq:
  forall m x,
  combine_r m = x ->
  match x with
  | Unchanged => tree_eq (PTree.Nodes m) (PTree.xcombine_r f (PTree.Nodes m))
  | Chempty => tree_eq PTree.Empty (PTree.xcombine_r f (PTree.Nodes m))
  | Changed m' => tree_eq (PTree.Nodes m') (PTree.xcombine_r f (PTree.Nodes m))
  end.
Proof.
intros.
pose proof (combine_r_eq' m); rewrite H in H0; destruct x; auto.
Qed.

Inductive changed2 : Type :=
  | Same
  | Same1
  | Same2
  | CC0
  | CC(m: PTree.tree' L.t).

Fixpoint xcombine (m1 m2 : PTree.tree' L.t) {struct m1} : changed2 :=
 match m1, m2 with
 | PTree.Node001 r1, PTree.Node001 r2 => 
     match xcombine r1 r2 with
     | Same => Same | Same1 => Same1 | Same2 => Same2 
     | CC0 => CC0
     | CC r => CC (PTree.Node001 r)
     end
 | PTree.Node001 r1, PTree.Node010 x2 => 
     match f None (Some x2), combine_l r1 with
     | None, Unchanged => Same1
     | None, Chempty => CC0
     | None, Changed r => CC (PTree.Node001 r)
     | Some x, Unchanged => if L.beq x x2 then CC (PTree.Node011 x2 r1) else CC (PTree.Node011 x r1)
     | Some x, Chempty => if L.beq x x2 then Same2 else CC (PTree.Node010 x)
     | Some x, Changed r => if L.beq x x2 then CC (PTree.Node011 x2 r) else CC (PTree.Node011 x r)
     end
 | PTree.Node001 r1, PTree.Node011 x2 r2 => 
     match f None (Some x2), xcombine r1 r2 with
     | None, Same => Same1
     | None, Same1 => Same1
     | None, Same2 => CC (PTree.Node001 r2)
     | None, CC0 => CC0
     | None, CC r => CC (PTree.Node001 r)
     | Some x, Same => if L.beq x x2 then Same2 else CC (PTree.Node011 x r2)
     | Some x, Same1 => if L.beq x x2 then CC (PTree.Node011 x2 r1) else CC (PTree.Node011 x r1)
     | Some x, Same2 => if L.beq x x2 then Same2 else CC (PTree.Node011 x r2)
     | Some x, CC0 => if L.beq x x2 then CC (PTree.Node010 x2) else CC (PTree.Node010 x)
     | Some x, CC r => if L.beq x x2 then CC (PTree.Node011 x2 r)  else CC (PTree.Node011 x r)
    end
 | PTree.Node001 r1, PTree.Node100 l2 => 
     match combine_r l2, combine_l r1 with
     | Unchanged, Unchanged => CC (PTree.Node101 l2 r1)
     | Unchanged, Chempty => Same2
     | Unchanged, Changed r => CC (PTree.Node101 l2 r)
     | Chempty, Unchanged => Same1
     | Chempty, Chempty => CC0
     | Chempty, Changed r => CC (PTree.Node001 r)
     | Changed l, Unchanged => CC (PTree.Node101 l r1)
     | Changed l, Chempty => CC (PTree.Node100 l)
     | Changed l, Changed r => CC (PTree.Node101 l r)
     end
 | PTree.Node001 r1, PTree.Node101 l2 r2 =>
     match combine_r l2, xcombine r1 r2 with
     | Unchanged, Same => Same2
     | Unchanged, Same1 => CC (PTree.Node101 l2 r1)
     | Unchanged, Same2 => Same2
     | Unchanged, CC0 => CC (PTree.Node100 l2)
     | Unchanged, CC r => CC (PTree.Node101 l2 r)
     | Chempty, Same => Same1
     | Chempty, Same1 => Same1
     | Chempty, Same2 => CC (PTree.Node001 r2)
     | Chempty, CC0 => CC0
     | Chempty, CC r => CC (PTree.Node001 r)
     | Changed l, Same => CC (PTree.Node101 l r1)
     | Changed l, Same1 => CC (PTree.Node101 l r1)
     | Changed l, Same2 => CC (PTree.Node101 l r2)
     | Changed l, CC0 => CC (PTree.Node100 l)
     | Changed l, CC r => CC (PTree.Node101 l r)
     end
 | PTree.Node001 r1, PTree.Node110 l2 x2 => 
    match combine_r l2, f None (Some x2), combine_l r1 with
    | Unchanged, None, Unchanged => CC (PTree.Node101 l2 r1)
    | Unchanged, None, Chempty => CC (PTree.Node100 l2)
    | Unchanged, None, Changed r => CC (PTree.Node101 l2 r)
    | Unchanged, Some x, Unchanged => if L.beq x x2 then CC (PTree.Node111 l2 x2 r1) else CC (PTree.Node111 l2 x r1)
    | Unchanged, Some x, Chempty =>  if L.beq x x2 then Same2 else CC (PTree.Node110 l2 x)
    | Unchanged, Some x, Changed r => if L.beq x x2 then CC (PTree.Node111 l2 x2 r) else CC (PTree.Node111 l2 x r)
    | Chempty, None, Unchanged => Same1
    | Chempty, None, Chempty => CC0
    | Chempty, None, Changed r => CC (PTree.Node001 r)
    | Chempty, Some x, Unchanged => if L.beq x x2 then CC (PTree.Node011 x2 r1) else CC (PTree.Node011 x r1)
    | Chempty, Some x, Chempty => if L.beq x x2 then CC (PTree.Node010 x2) else CC (PTree.Node010 x)
    | Chempty, Some x, Changed r => if L.beq x x2 then CC (PTree.Node011 x2 r) else CC (PTree.Node011 x r)
    | Changed l, None, Unchanged => CC (PTree.Node101 l r1)
    | Changed l, None, Chempty => CC (PTree.Node100 l)
    | Changed l, None, Changed r => CC (PTree.Node101 l r)
    | Changed l, Some x, Unchanged => if L.beq x x2 then CC (PTree.Node111 l x2 r1) else CC (PTree.Node111 l x r1)
    | Changed l, Some x, Chempty =>  if L.beq x x2 then CC (PTree.Node110 l x2) else CC (PTree.Node110 l x)
    | Changed l, Some x, Changed r => if L.beq x x2 then CC (PTree.Node111 l x2 r) else CC (PTree.Node111 l x r)
   end
 | PTree.Node001 r1, PTree.Node111 l2 x2 r2 =>
     match combine_r l2, f None (Some x2), xcombine r1 r2 with
     | Unchanged, None, Same => CC (PTree.Node101 l2 r2)
     | Unchanged, None, Same1 => CC (PTree.Node101 l2 r1)
     | Unchanged, None, Same2 => CC (PTree.Node101 l2 r2)
     | Unchanged, None, CC0 => CC (PTree.Node100 l2)
     | Unchanged, None, CC r => CC (PTree.Node101 l2 r)
     | Unchanged, Some x, Same => if L.beq x x2 then Same2 else CC (PTree.Node111 l2 x r2)
     | Unchanged, Some x, Same1 => if L.beq x x2 then CC (PTree.Node111 l2 x2 r1) else CC (PTree.Node111 l2 x r1)
     | Unchanged, Some x, Same2 => if L.beq x x2 then Same2 else CC (PTree.Node111 l2 x r2)
     | Unchanged, Some x, CC0 => if L.beq x x2 then CC (PTree.Node110 l2 x2) else CC (PTree.Node110 l2 x)
     | Unchanged, Some x, CC r => if L.beq x x2 then CC (PTree.Node111 l2 x2 r)  else CC (PTree.Node111 l2 x r)
     | Chempty, None, Same => Same1
     | Chempty, None, Same1 => Same1
     | Chempty, None, Same2 => CC (PTree.Node001 r2)
     | Chempty, None, CC0 => CC0
     | Chempty, None, CC r => CC (PTree.Node001 r)
     | Chempty, Some x, Same => if L.beq x x2 then CC (PTree.Node011 x2 r2) else CC (PTree.Node011 x r2)
     | Chempty, Some x, Same1 => if L.beq x x2 then CC (PTree.Node011 x2 r1) else CC (PTree.Node011 x r1)
     | Chempty, Some x, Same2 => if L.beq x x2 then CC (PTree.Node011 x2 r2) else CC (PTree.Node011 x r2)
     | Chempty, Some x, CC0 => if L.beq x x2 then CC (PTree.Node010 x2) else CC (PTree.Node010 x)
     | Chempty, Some x, CC r => if L.beq x x2 then CC (PTree.Node011 x2 r)  else CC (PTree.Node011 x r)
     | Changed l, None, Same => CC (PTree.Node101 l r2)
     | Changed l, None, Same1 => CC (PTree.Node101 l r1)
     | Changed l, None, Same2 => CC (PTree.Node101 l r2)
     | Changed l, None, CC0 => CC (PTree.Node100 l)
     | Changed l, None, CC r => CC (PTree.Node101 l r)
     | Changed l, Some x, Same => if L.beq x x2 then CC(PTree.Node111 l x2 r2) else CC (PTree.Node111 l x r2)
     | Changed l, Some x, Same1 => if L.beq x x2 then CC (PTree.Node111 l x2 r1) else CC (PTree.Node111 l x r1)
     | Changed l, Some x, Same2 => if L.beq x x2 then CC (PTree.Node111 l x2 r2) else CC (PTree.Node111 l x r2)
     | Changed l, Some x, CC0 => if L.beq x x2 then CC (PTree.Node110 l x2) else CC (PTree.Node110 l x)
     | Changed l, Some x, CC r => if L.beq x x2 then CC (PTree.Node111 l x2 r)  else CC (PTree.Node111 l x r)
    end
 | PTree.Node010 x1, PTree.Node001 r2 => 
    match f (Some x1) None, combine_r r2 with
    | None, Unchanged => Same2
    | None, Chempty => CC0
    | None, Changed r => CC (PTree.Node001 r)
    | Some x, Unchanged => if L.beq x x1 then CC (PTree.Node011 x1 r2) else  CC (PTree.Node011 x r2)
    | Some x, Chempty => if L.beq x x1 then Same1 else CC (PTree.Node010 x)
    | Some x, Changed r => if L.beq x x1 then CC (PTree.Node011 x1 r) else CC (PTree.Node011 x r)
   end
 | PTree.Node010 x1, PTree.Node010 x2 => 
    match f (Some x1)  (Some x2) with
    | None => CC0
    | Some x => match L.beq x x1, L.beq x x2 with
                         | true, true => Same2
                         | true, false => Same1
                         | false, true => Same2
                         | false, false => CC (PTree.Node010 x)
                         end
    end
 | PTree.Node010 x1, PTree.Node011 x2 r2 =>
    match f (Some x1) (Some x2), combine_r r2 with
    | None, Unchanged => CC (PTree.Node001 r2)
    | None, Chempty => CC0
    | None, Changed r => CC (PTree.Node001 r)
    | Some x, Unchanged => if L.beq x x2 then Same2 else if L.beq x x1 then CC (PTree.Node011 x1 r2) else CC (PTree.Node011 x r2)
    | Some x, Chempty => if L.beq x x1 then Same1 else if L.beq x x2 then CC (PTree.Node010 x2) else CC (PTree.Node010 x)
    | Some x, Changed r => if L.beq x x1 then CC (PTree.Node011 x1 r) else if L.beq x x2 then CC (PTree.Node011 x2 r) else CC (PTree.Node011 x r)
    end
 | PTree.Node010 x1, PTree.Node100 l2 => 
    match combine_r l2, f (Some x1) None with
    | Unchanged, None => Same2
    | Unchanged, Some x => if L.beq x x1 then CC (PTree.Node110 l2 x1) else  CC (PTree.Node110 l2 x)
    | Chempty, None => CC0
    | Chempty, Some x => if L.beq x x1 then Same1 else CC (PTree.Node010 x)
    | Changed l, None => CC (PTree.Node100 l)
    | Changed l, Some x => if L.beq x x1 then CC (PTree.Node110 l x1) else CC (PTree.Node110 l x)
   end
 | PTree.Node010 x1, PTree.Node101 l2 r2 =>
    match combine_r l2, f (Some x1) None, combine_r r2 with
    | Unchanged, None, Unchanged => Same2
    | Unchanged, None, Chempty => CC (PTree.Node100 l2)
    | Unchanged, None, Changed r => CC (PTree.Node101 l2 r)
    | Unchanged, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node111 l2 x1 r2) else CC (PTree.Node111 l2 x r2)
    | Unchanged, Some x, Chempty => if L.beq x x1 then CC (PTree.Node110 l2 x1) else CC (PTree.Node110 l2 x)
    | Unchanged, Some x, Changed r => if L.beq x x1 then CC (PTree.Node111 l2 x1 r) else CC (PTree.Node111 l2 x r)
    | Chempty, None, Unchanged => CC (PTree.Node001 r2)
    | Chempty, None, Chempty => CC0
    | Chempty, None, Changed r => CC (PTree.Node001 r)
    | Chempty, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node011 x1 r2) else CC (PTree.Node011 x r2)
    | Chempty, Some x, Chempty => if L.beq x x1 then Same1 else CC (PTree.Node010 x)
    | Chempty, Some x, Changed r => if L.beq x x1 then CC (PTree.Node011 x1 r) else CC (PTree.Node011 x r)
    | Changed l, None, Unchanged => CC (PTree.Node101 l r2)
    | Changed l, None, Chempty => CC (PTree.Node100 l)
    | Changed l, None, Changed r => CC (PTree.Node101 l r)
    | Changed l, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node111 l x1 r2) else CC (PTree.Node111 l x r2)
    | Changed l, Some x, Chempty => if L.beq x x1 then CC (PTree.Node110 l x1) else CC (PTree.Node110 l x)
    | Changed l, Some x, Changed r => if L.beq x x1 then CC (PTree.Node111 l x1 r) else CC (PTree.Node111 l x r)
   end
 | PTree.Node010 x1, PTree.Node110 l2 x2 =>
    match combine_r l2, f (Some x1) (Some x2) with
    | Unchanged, None => CC (PTree.Node100 l2)
    | Unchanged, Some x => if L.beq x x2 then Same2 else if L.beq x x1 then CC (PTree.Node110 l2 x1) else CC (PTree.Node110 l2 x)
    | Chempty, None => CC0
    | Chempty, Some x => if L.beq x x1 then Same1 else if L.beq x x2 then CC (PTree.Node010 x2) else CC (PTree.Node010 x)
    | Changed l, None => CC (PTree.Node100 l)
    | Changed l, Some x => if L.beq x x1 then CC (PTree.Node110 l x1) else if L.beq x x2 then CC (PTree.Node110 l x2) else CC (PTree.Node110 l x)
    end
 | PTree.Node010 x1, PTree.Node111 l2 x2 r2 =>
    match combine_r l2, f (Some x1) (Some x2), combine_r r2 with
    | Unchanged, None, Unchanged => CC (PTree.Node101 l2 r2)
    | Unchanged, None, Chempty => CC (PTree.Node100 l2)
    | Unchanged, None, Changed r => CC (PTree.Node101 l2 r)
    | Unchanged, Some x, Unchanged => if L.beq x x2 then Same2 else if L.beq x x1 then CC (PTree.Node111 l2 x1 r2) else CC (PTree.Node111 l2 x r2)
    | Unchanged, Some x, Chempty => if L.beq x x1 then CC (PTree.Node110 l2 x1) else if L.beq x x2 then CC (PTree.Node110 l2 x2) else CC (PTree.Node110 l2 x)
    | Unchanged, Some x, Changed r =>  if L.beq x x1 then CC (PTree.Node111 l2 x1 r) else if L.beq x x2 then CC (PTree.Node111 l2 x2 r) else CC (PTree.Node111 l2 x r)
    | Chempty, None, Unchanged => CC (PTree.Node001 r2)
    | Chempty, None, Chempty => CC0
    | Chempty, None, Changed r => CC (PTree.Node001 r)
    | Chempty, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node011 x1 r2) else if L.beq x x2 then CC (PTree.Node011 x2 r2) else CC (PTree.Node011 x r2)
    | Chempty, Some x, Chempty => if L.beq x x1 then Same1 else if L.beq x x2 then CC (PTree.Node010 x2) else CC (PTree.Node010 x)
    | Chempty, Some x, Changed r => if L.beq x x1 then CC (PTree.Node011 x1 r) else if L.beq x x2 then CC (PTree.Node011 x2 r) else CC (PTree.Node011 x r)
    | Changed l, None, Unchanged => CC (PTree.Node101 l r2)
    | Changed l, None, Chempty => CC (PTree.Node100 l)
    | Changed l, None, Changed r => CC (PTree.Node101 l r)
    | Changed l, Some x, Unchanged => if L.beq x x2 then CC (PTree.Node111 l x2 r2) else if L.beq x x1 then CC (PTree.Node111 l x1 r2) else CC (PTree.Node111 l x r2)
    | Changed l, Some x, Chempty => if L.beq x x1 then CC (PTree.Node110 l x1) else if L.beq x x2 then CC (PTree.Node110 l x2) else CC (PTree.Node110 l x)
    | Changed l, Some x, Changed r =>  if L.beq x x1 then CC (PTree.Node111 l x1 r) else if L.beq x x2 then CC (PTree.Node111 l x2 r) else CC (PTree.Node111 l x r)
   end
 | PTree.Node011 x1 r1, PTree.Node001 r2 =>
    match f (Some x1) None, xcombine r1 r2 with
    | None, Same => Same2
    | None, Same1 => CC (PTree.Node001 r1)
    | None, Same2 => Same2
    | None, CC0 => CC0
    | None, CC r => CC (PTree.Node001 r)
    | Some x, Same => if L.beq x x1 then Same1 else CC (PTree.Node011 x r1)
    | Some x, Same1 => if L.beq x x1 then Same1 else CC (PTree.Node011 x r1)
    | Some x, Same2 => if L.beq x x1 then CC (PTree.Node011 x1 r2) else CC (PTree.Node011 x r2)
    | Some x, CC0 => if L.beq x x1 then CC (PTree.Node010 x1) else CC (PTree.Node010 x)
    | Some x, CC r => if L.beq x x1 then CC (PTree.Node011 x1 r) else CC (PTree.Node011 x r)
   end
 | PTree.Node011 x1 r1, PTree.Node010 x2 =>
   match f (Some x1) (Some x2), combine_l r1 with
   | None, Unchanged => CC (PTree.Node001 r1)
   | None, Chempty => CC0
   | None, Changed r => CC (PTree.Node001 r)
   | Some x, Unchanged => if L.beq x x1 then Same1 else if L.beq x x2 then CC (PTree.Node011 x2 r1) else CC (PTree.Node011 x r1)
   | Some x, Chempty => if L.beq x x2 then Same2 else if L.beq x x1 then CC (PTree.Node010 x1) else CC (PTree.Node010 x)
   | Some x, Changed r => if L.beq x x1 then CC (PTree.Node011 x1 r) else if L.beq x x2 then CC (PTree.Node011 x2 r) else CC (PTree.Node011 x r)
  end
 | PTree.Node011 x1 r1, PTree.Node011 x2 r2 =>
   match f (Some x1) (Some x2), xcombine r1 r2 with
   | None, Same => CC (PTree.Node001 r1)
   | None, Same1 => CC (PTree.Node001 r1)
   | None, Same2 => CC (PTree.Node001 r2)
   | None, CC0 => CC0
   | None, CC r => CC (PTree.Node001 r)
   | Some x, Same => if L.beq x x1 then Same1 else if L.beq x x2 then Same2 else CC (PTree.Node011 x r1)
   | Some x, Same1 => if L.beq x x1 then Same1 else if L.beq x x2 then CC (PTree.Node011 x2 r1) else CC (PTree.Node011 x r1)
   | Some x, Same2 => if L.beq x x2 then Same2 else if L.beq x x1 then CC (PTree.Node011 x1 r2) else CC (PTree.Node011 x r2)
   | Some x, CC0 => if L.beq x x1 then CC (PTree.Node010 x1) else if L.beq x x2 then CC (PTree.Node010 x2) else CC (PTree.Node010 x)
   | Some x, CC r => if L.beq x x1 then CC (PTree.Node011 x1 r) else if L.beq x x2 then CC (PTree.Node011 x2 r) else CC (PTree.Node011 x r)
  end
 | PTree.Node011 x1 r1, PTree.Node100 l2 =>
  match combine_r l2, f (Some x1) None, combine_l r1 with
  | Unchanged, None, Unchanged => CC (PTree.Node101 l2 r1)
  | Unchanged, None, Chempty => Same2
  | Unchanged, None, Changed r => CC (PTree.Node101 l2 r)
  | Unchanged, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node111 l2 x1 r1) else CC (PTree.Node111 l2 x r1)
  | Unchanged, Some x, Chempty => if L.beq x x1 then CC (PTree.Node110 l2 x1) else CC (PTree.Node110 l2 x)
  | Unchanged, Some x, Changed r => if L.beq x x1 then CC (PTree.Node111 l2 x1 r) else CC (PTree.Node111 l2 x r)
  | Chempty, None, Unchanged => CC (PTree.Node001 r1)
  | Chempty, None, Chempty => CC0
  | Chempty, None, Changed r => CC (PTree.Node001 r)
  | Chempty, Some x, Unchanged => if L.beq x x1 then Same1 else CC (PTree.Node011 x r1)
  | Chempty, Some x, Chempty => if L.beq x x1 then CC (PTree.Node010 x1) else CC (PTree.Node010 x)
  | Chempty, Some x, Changed r =>  if L.beq x x1 then CC (PTree.Node011 x1 r) else CC (PTree.Node011 x r)
  | Changed l, None, Unchanged => CC (PTree.Node101 l r1)
  | Changed l, None, Chempty => CC (PTree.Node100 l)
  | Changed l, None, Changed r => CC (PTree.Node101 l r)
  | Changed l, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node111 l x1 r1) else CC (PTree.Node111 l x r1)
  | Changed l, Some x, Chempty => if L.beq x x1 then CC (PTree.Node110 l x1) else CC (PTree.Node110 l x)
  | Changed l, Some x, Changed r => if L.beq x x1 then CC (PTree.Node111 l x1 r) else CC (PTree.Node111 l x r)
 end
 | PTree.Node011 x1 r1, PTree.Node101 l2 r2 =>
 match combine_r l2, f (Some x1) None, xcombine r1 r2 with
  | Unchanged, None, Same => Same2
  | Unchanged, None, Same1 => CC (PTree.Node101 l2 r1)
  | Unchanged, None, Same2 => Same2
  | Unchanged, None, CC0 => CC (PTree.Node100 l2)
  | Unchanged, None, CC r => CC (PTree.Node101 l2 r)
  | Unchanged, Some x, Same => if L.beq x x1 then CC (PTree.Node111 l2 x1 r1) else CC (PTree.Node111 l2 x r1)
  | Unchanged, Some x, Same1 => if L.beq x x1 then CC (PTree.Node111 l2 x1 r1) else CC (PTree.Node111 l2 x r1)
  | Unchanged, Some x, Same2 => if L.beq x x1 then CC (PTree.Node111 l2 x1 r2) else CC (PTree.Node111 l2 x r2)
  | Unchanged, Some x, CC0 => if L.beq x x1 then CC (PTree.Node110 l2 x1) else CC (PTree.Node110 l2 x)
  | Unchanged, Some x, CC r => if L.beq x x1 then CC (PTree.Node111 l2 x1 r) else CC (PTree.Node111 l2 x r)
  | Chempty, None, Same => CC (PTree.Node001 r2)
  | Chempty, None, Same1 => CC (PTree.Node001 r1)
  | Chempty, None, Same2 => CC (PTree.Node001 r2)
  | Chempty, None, CC0 => CC0
  | Chempty, None, CC r => CC (PTree.Node001 r)
  | Chempty, Some x, Same => if L.beq x x1 then Same1 else CC (PTree.Node011 x r1)
  | Chempty, Some x, Same1 => if L.beq x x1 then Same1 else CC (PTree.Node011 x r1)
  | Chempty, Some x, Same2 => if L.beq x x1 then CC (PTree.Node011 x1 r2) else CC (PTree.Node011 x r2)
  | Chempty, Some x, CC0 => if L.beq x x1 then CC (PTree.Node010 x1) else CC (PTree.Node010 x)
  | Chempty, Some x, CC r =>  if L.beq x x1 then CC (PTree.Node011 x1 r) else CC (PTree.Node011 x r)
  | Changed l, None, Same => CC (PTree.Node101 l r2)
  | Changed l, None, Same1 => CC (PTree.Node101 l r1)
  | Changed l, None, Same2 => CC (PTree.Node101 l r2)
  | Changed l, None, CC0 => CC (PTree.Node100 l)
  | Changed l, None, CC r => CC (PTree.Node101 l r)
  | Changed l, Some x, Same => if L.beq x x1 then CC (PTree.Node111 l x1 r1) else CC (PTree.Node111 l x r1)
  | Changed l, Some x, Same1 => if L.beq x x1 then CC (PTree.Node111 l x1 r1) else CC (PTree.Node111 l x r1)
  | Changed l, Some x, Same2 => if L.beq x x1 then CC (PTree.Node111 l x1 r2) else CC (PTree.Node111 l x r2)
  | Changed l, Some x, CC0 => if L.beq x x1 then CC (PTree.Node110 l x1) else CC (PTree.Node110 l x)
  | Changed l, Some x, CC r => if L.beq x x1 then CC (PTree.Node111 l x1 r) else CC (PTree.Node111 l x r)
 end
 | PTree.Node011 x1 r1, PTree.Node110 l2 x2 =>
 match combine_r l2, f (Some x1) (Some x2), combine_l r1 with
  | Unchanged, None, Unchanged => CC (PTree.Node101 l2 r1)
  | Unchanged, None, Chempty => CC (PTree.Node100 l2)
  | Unchanged, None, Changed r => CC (PTree.Node101 l2 r)
  | Unchanged, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node111 l2 x1 r1) else if L.beq x x2 then CC (PTree.Node111 l2 x2 r1) else CC (PTree.Node111 l2 x r1)
  | Unchanged, Some x, Chempty => if L.beq x x1 then CC (PTree.Node110 l2 x1) else if L.beq x x2 then CC (PTree.Node110 l2 x2) else CC (PTree.Node110 l2 x)
  | Unchanged, Some x, Changed r => if L.beq x x1 then CC (PTree.Node111 l2 x1 r) else if L.beq x x2 then CC (PTree.Node111 l2 x2 r) else CC (PTree.Node111 l2 x r)
  | Chempty, None, Unchanged => CC (PTree.Node001 r1)
  | Chempty, None, Chempty => CC0
  | Chempty, None, Changed r => CC (PTree.Node001 r)
  | Chempty, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node011 x1 r1) else if L.beq x x2 then CC (PTree.Node011 x2 r1) else CC (PTree.Node011 x r1)
  | Chempty, Some x, Chempty => if L.beq x x1 then CC (PTree.Node010 x1) else if L.beq x x2 then CC (PTree.Node010 x2) else CC (PTree.Node010 x)
  | Chempty, Some x, Changed r =>  if L.beq x x1 then CC (PTree.Node011 x1 r) else if L.beq x x2 then CC (PTree.Node011 x2 r) else  CC (PTree.Node011 x r)
  | Changed l, None, Unchanged => CC (PTree.Node101 l r1)
  | Changed l, None, Chempty => CC (PTree.Node100 l)
  | Changed l, None, Changed r => CC (PTree.Node101 l r)
  | Changed l, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node111 l x1 r1) else if L.beq x x2 then CC (PTree.Node111 l x2 r1) else CC (PTree.Node111 l x r1)
  | Changed l, Some x, Chempty => if L.beq x x1 then CC (PTree.Node110 l x1) else CC (PTree.Node110 l x)
  | Changed l, Some x, Changed r => if L.beq x x1 then CC (PTree.Node111 l x1 r) else CC (PTree.Node111 l x r)
 end
 | PTree.Node011 x1 r1, PTree.Node111 l2 x2 r2 =>
 match combine_r l2, f (Some x1) (Some x2), xcombine r1 r2 with
  | Unchanged, None, Same => CC (PTree.Node101 l2 r2)
  | Unchanged, None, Same1 => CC (PTree.Node101 l2 r1)
  | Unchanged, None, Same2 => CC (PTree.Node101 l2 r2)
  | Unchanged, None, CC0 => CC (PTree.Node100 l2)
  | Unchanged, None, CC r => CC (PTree.Node101 l2 r)
  | Unchanged, Some x, Same => if L.beq x x1 then CC (PTree.Node111 l2 x1 r1) else if L.beq x x2 then Same2 else CC (PTree.Node111 l2 x r2)
  | Unchanged, Some x, Same1 => if L.beq x x1 then CC (PTree.Node111 l2 x1 r1) else CC (PTree.Node111 l2 x r1)
  | Unchanged, Some x, Same2 => if L.beq x x1 then CC (PTree.Node111 l2 x1 r2) else if L.beq x x2 then CC (PTree.Node111 l2 x2 r2) else CC (PTree.Node111 l2 x r2)
  | Unchanged, Some x, CC0 => if L.beq x x1 then CC (PTree.Node110 l2 x1) else if L.beq x x2 then CC (PTree.Node110 l2 x2) else CC (PTree.Node110 l2 x)
  | Unchanged, Some x, CC r => if L.beq x x1 then CC (PTree.Node111 l2 x1 r) else if L.beq x x2 then CC (PTree.Node111 l2 x2 r) else CC (PTree.Node111 l2 x r)
  | Chempty, None, Same => CC (PTree.Node001 r2)
  | Chempty, None, Same1 => CC (PTree.Node001 r1)
  | Chempty, None, Same2 => CC (PTree.Node001 r2)
  | Chempty, None, CC0 => CC0
  | Chempty, None, CC r => CC (PTree.Node001 r)
  | Chempty, Some x, Same => if L.beq x x1 then Same1 else if L.beq x x2 then CC (PTree.Node011 x2 r1) else CC (PTree.Node011 x r1)
  | Chempty, Some x, Same1 => if L.beq x x1 then Same1 else if L.beq x x2 then CC (PTree.Node011 x2 r1) else CC (PTree.Node011 x r1)
  | Chempty, Some x, Same2 => if L.beq x x1 then CC (PTree.Node011 x1 r2) else if L.beq x x2 then CC (PTree.Node011 x2 r2) else CC (PTree.Node011 x r2)
  | Chempty, Some x, CC0 => if L.beq x x1 then CC (PTree.Node010 x1) else if L.beq x x2 then CC (PTree.Node010 x2) else CC (PTree.Node010 x)
  | Chempty, Some x, CC r =>  if L.beq x x1 then CC (PTree.Node011 x1 r) else if L.beq x x2 then CC (PTree.Node011 x2 r) else CC (PTree.Node011 x r)
  | Changed l, None, Same => CC (PTree.Node101 l r2)
  | Changed l, None, Same1 => CC (PTree.Node101 l r1)
  | Changed l, None, Same2 => CC (PTree.Node101 l r2)
  | Changed l, None, CC0 => CC (PTree.Node100 l)
  | Changed l, None, CC r => CC (PTree.Node101 l r)
  | Changed l, Some x, Same => if L.beq x x1 then CC (PTree.Node111 l x1 r1) else if L.beq x x2 then CC (PTree.Node111 l x2 r1) else CC (PTree.Node111 l x r1)
  | Changed l, Some x, Same1 => if L.beq x x1 then CC (PTree.Node111 l x1 r1) else if L.beq x x2 then CC (PTree.Node111 l x2 r1) else CC (PTree.Node111 l x r1)
  | Changed l, Some x, Same2 => if L.beq x x1 then CC (PTree.Node111 l x1 r2) else if L.beq x x2 then CC (PTree.Node111 l x2 r2) else CC (PTree.Node111 l x r2)
  | Changed l, Some x, CC0 => if L.beq x x1 then CC (PTree.Node110 l x1) else if L.beq x x2 then CC (PTree.Node110 l x2) else CC (PTree.Node110 l x)
  | Changed l, Some x, CC r => if L.beq x x1 then CC (PTree.Node111 l x1 r) else if L.beq x x2 then CC (PTree.Node111 l x2 r) else CC (PTree.Node111 l x r)
 end
 | PTree.Node100 l1, PTree.Node001 r2 =>
  match combine_l l1, combine_r r2 with
  | Unchanged, Unchanged => CC (PTree.Node101 l1 r2)
  | Unchanged, Chempty => Same1
  | Unchanged, Changed r => CC (PTree.Node101 l1 r)
  | Chempty, Unchanged => Same2
  | Chempty, Chempty => CC0
  | Chempty, Changed r => CC (PTree.Node001 r)
  | Changed l, Unchanged => CC (PTree.Node101 l r2)
  | Changed l, Chempty => CC (PTree.Node100 l)
  | Changed l, Changed r => CC (PTree.Node101 l r)
  end
 | PTree.Node100 l1, PTree.Node010 x2 =>
  match combine_l l1, f None (Some x2) with
  | Unchanged, None => Same1
  | Unchanged, Some x => if L.beq x x2 then CC (PTree.Node110 l1 x2) else CC (PTree.Node110 l1 x)
  | Chempty, None => CC0
  | Chempty, Some x => if L.beq x x2 then Same2 else CC (PTree.Node010 x)
  | Changed l, None => CC (PTree.Node100 l)
  | Changed l, Some x => if L.beq x x2 then CC (PTree.Node110 l x2) else CC (PTree.Node110 l x)
  end
 | PTree.Node100 l1, PTree.Node011 x2 r2 =>
   match combine_l l1, f None (Some x2), combine_r r2 with
  | Unchanged, None, Unchanged => CC (PTree.Node101 l1 r2)
  | Unchanged, None, Chempty => Same1
  | Unchanged, None, Changed r => CC (PTree.Node101 l1 r)
  | Unchanged, Some x, Unchanged => if L.beq x x2 then CC (PTree.Node111 l1 x2 r2) else CC (PTree.Node111 l1 x r2)
  | Unchanged, Some x, Chempty => if L.beq x x2 then CC (PTree.Node110 l1 x2) else CC (PTree.Node110 l1 x)
  | Unchanged, Some x, Changed r => if L.beq x x2 then CC (PTree.Node111 l1 x2 r) else CC (PTree.Node111 l1 x r)
  | Chempty, None, Unchanged => CC (PTree.Node001 r2)
  | Chempty, None, Chempty => CC0
  | Chempty, None, Changed r => CC (PTree.Node001 r)
  | Chempty, Some x, Unchanged => if L.beq x x2 then CC (PTree.Node011 x2 r2) else CC (PTree.Node011 x r2)
  | Chempty, Some x, Chempty => if L.beq x x2 then CC (PTree.Node010 x2) else CC (PTree.Node010 x)
  | Chempty, Some x, Changed r =>  if L.beq x x2 then CC (PTree.Node011 x2 r) else CC (PTree.Node011 x r)
  | Changed l, None, Unchanged => CC (PTree.Node101 l r2)
  | Changed l, None, Chempty => CC (PTree.Node100 l)
  | Changed l, None, Changed r => CC (PTree.Node101 l r)
  | Changed l, Some x, Unchanged => if L.beq x x2 then CC (PTree.Node111 l x2 r2) else CC (PTree.Node111 l x r2)
  | Changed l, Some x, Chempty => if L.beq x x2 then CC (PTree.Node110 l x2) else CC (PTree.Node110 l x)
  | Changed l, Some x, Changed r => if L.beq x x2 then CC (PTree.Node111 l x2 r) else CC (PTree.Node111 l x r)
 end
 | PTree.Node100 l1, PTree.Node100 l2 =>
  match xcombine l1 l2 with
  | Same => Same
  | Same1 => Same1
  | Same2 => Same2
  | CC0 => CC0
  | CC l => CC (PTree.Node100 l)
  end
 | PTree.Node100 l1, PTree.Node101 l2 r2 =>
  match xcombine l1 l2, combine_r r2 with
  | Same, Unchanged => Same2
  | Same, Chempty => Same1
  | Same, Changed r => CC (PTree.Node101 l2 r)
  | Same1, Unchanged => CC (PTree.Node101 l1 r2)
  | Same1, Chempty => Same1
  | Same1, Changed r => CC (PTree.Node101 l1 r)
  | Same2, Unchanged => Same2
  | Same2, Chempty => CC (PTree.Node100 l2)
  | Same2, Changed r => CC (PTree.Node101 l2 r)
  | CC0, Unchanged => CC (PTree.Node001 r2)
  | CC0, Chempty => CC0
  | CC0, Changed r => CC (PTree.Node001 r)
  | CC l, Unchanged => CC (PTree.Node101 l r2)
  | CC l, Chempty => CC (PTree.Node100 l)
  | CC l, Changed r => CC (PTree.Node101 l r)
  end
 | PTree.Node100 l1, PTree.Node110 l2 x2 =>
  match xcombine l1 l2, f None (Some x2) with
  | Same, None => Same1
  | Same, Some x => if L.beq x x2 then Same2 else CC (PTree.Node110 l2 x)
  | Same1, None => Same1
  | Same1, Some x => if L.beq x x2 then CC (PTree.Node110 l1 x2) else CC (PTree.Node110 l1 x)
  | Same2, None => CC (PTree.Node100 l2)
  | Same2, Some x => if L.beq x x2 then Same2 else CC (PTree.Node110 l2 x)
  | CC0, None => CC0
  | CC0, Some x => if L.beq x x2 then CC (PTree.Node010 x2) else CC (PTree.Node010 x)
  | CC l, None => CC (PTree.Node100 l)
  | CC l, Some x => if L.beq x x2 then CC (PTree.Node110 l x2) else CC (PTree.Node110 l x)
  end
 | PTree.Node100 l1, PTree.Node111 l2 x2 r2 =>
  match xcombine l1 l2, f None (Some x2), combine_r r2 with
  | Same, None, Unchanged => CC (PTree.Node101 l2 r2)
  | Same, None, Chempty => Same1
  | Same, None, Changed r => CC (PTree.Node101 l2 r)
  | Same, Some x, Unchanged => if L.beq x x2 then Same2 else CC (PTree.Node111 l2 x r2)
  | Same, Some x, Chempty => if L.beq x x2 then CC (PTree.Node110 l2 x2) else CC (PTree.Node110 l2 x)
  | Same, Some x, Changed r => if L.beq x x2 then CC (PTree.Node111 l2 x2 r) else CC (PTree.Node111 l2 x r)
  | Same1, None, Unchanged => CC (PTree.Node101 l1 r2)
  | Same1, None, Chempty => Same1
  | Same1, None, Changed r => CC (PTree.Node101 l1 r)
  | Same1, Some x, Unchanged => if L.beq x x2 then CC (PTree.Node111 l1 x2 r2) else CC (PTree.Node111 l1 x r2)
  | Same1, Some x, Chempty => if L.beq x x2 then CC (PTree.Node110 l1 x2) else CC (PTree.Node110 l1 x)
  | Same1, Some x, Changed r => if L.beq x x2 then CC (PTree.Node111 l1 x2 r) else CC (PTree.Node111 l1 x r)
  | Same2, None, Unchanged => CC (PTree.Node101 l2 r2)
  | Same2, None, Chempty =>CC (PTree.Node100 l2)
  | Same2, None, Changed r => CC (PTree.Node101 l2 r)
  | Same2, Some x, Unchanged => if L.beq x x2 then Same2 else CC (PTree.Node111 l2 x r2)
  | Same2, Some x, Chempty => if L.beq x x2 then CC (PTree.Node110 l2 x2) else CC (PTree.Node110 l2 x)
  | Same2, Some x, Changed r => if L.beq x x2 then CC (PTree.Node111 l2 x2 r) else CC (PTree.Node111 l2 x r)
  | CC0, None, Unchanged => CC (PTree.Node001 r2)
  | CC0, None, Chempty => CC0
  | CC0, None, Changed r => CC (PTree.Node001 r)
  | CC0, Some x, Unchanged => if L.beq x x2 then CC (PTree.Node011 x2 r2) else CC (PTree.Node011 x r2)
  | CC0, Some x, Chempty => if L.beq x x2 then CC (PTree.Node010 x2) else CC (PTree.Node010 x)
  | CC0, Some x, Changed r => if L.beq x x2 then CC (PTree.Node011 x2 r) else CC (PTree.Node011 x r)
  | CC l, None, Unchanged => CC (PTree.Node101 l r2)
  | CC l, None, Chempty => CC (PTree.Node100 l)
  | CC l, None, Changed r => CC (PTree.Node101 l r)
  | CC l, Some x, Unchanged => if L.beq x x2 then CC (PTree.Node111 l x2 r2) else CC (PTree.Node111 l x r2)
  | CC l, Some x, Chempty => if L.beq x x2 then CC (PTree.Node110 l x2) else CC (PTree.Node110 l x)
  | CC l, Some x, Changed r => if L.beq x x2 then CC (PTree.Node111 l x2 r) else CC (PTree.Node111 l x r)
  end
 | PTree.Node101 l1 r1, PTree.Node001 r2 =>
  match combine_l l1, xcombine r1 r2 with
  | Unchanged, Same => Same1
  | Unchanged, Same1 => Same1
  | Unchanged, Same2 => CC (PTree.Node101 l1 r2)
  | Unchanged, CC0 => CC (PTree.Node100 l1)
  | Unchanged, CC r => CC (PTree.Node101 l1 r)
  | Chempty, Same => Same2
  | Chempty, Same1 => CC (PTree.Node001 r1)
  | Chempty, Same2 => Same2
  | Chempty, CC0 => CC0
  | Chempty, CC r => CC (PTree.Node001 r)
  | Changed l, Same => CC (PTree.Node101 l r2)
  | Changed l, Same1 => CC (PTree.Node101 l r1)
  | Changed l, Same2 => CC (PTree.Node101 l r2)
  | Changed l, CC0 => CC (PTree.Node100 l)
  | Changed l, CC r => CC (PTree.Node101 l r)
  end

 | PTree.Node101 l1 r1, PTree.Node010 x2 =>
  match combine_l l1, f None (Some x2), combine_l r1 with
  | Unchanged, None, Unchanged => Same1
  | Unchanged, None, Chempty => CC (PTree.Node100 l1)
  | Unchanged, None, Changed r => CC (PTree.Node101 l1 r)
  | Unchanged, Some x, Unchanged => if L.beq x x2 then CC (PTree.Node111 l1 x2 r1) else CC (PTree.Node111 l1 x r1)
  | Unchanged, Some x, Chempty => if L.beq x x2 then CC (PTree.Node110 l1 x2) else CC (PTree.Node110 l1 x)
  | Unchanged, Some x, Changed r => if L.beq x x2 then CC (PTree.Node111 l1 x2 r) else CC (PTree.Node111 l1 x r)
  | Chempty, None, Unchanged => CC (PTree.Node001 r1)
  | Chempty, None, Chempty => CC0
  | Chempty, None, Changed r => CC (PTree.Node001 r)
  | Chempty, Some x, Unchanged => if L.beq x x2 then CC (PTree.Node011 x2 r1) else CC (PTree.Node011 x r1)
  | Chempty, Some x, Chempty => if L.beq x x2 then Same2 else CC (PTree.Node010 x)
  | Chempty, Some x, Changed r => if L.beq x x2 then CC (PTree.Node011 x2 r) else CC (PTree.Node011 x r)
  | Changed l, None, Unchanged => CC (PTree.Node101 l r1)
  | Changed l, None, Chempty => CC (PTree.Node100 l)
  | Changed l, None, Changed r => CC (PTree.Node101 l r)
  | Changed l, Some x, Unchanged => if L.beq x x2 then CC (PTree.Node111 l x2 r1) else CC (PTree.Node111 l x r1)
  | Changed l, Some x, Chempty => if L.beq x x2 then CC (PTree.Node110 l x2) else CC (PTree.Node110 l x)
  | Changed l, Some x, Changed r => if L.beq x x2 then CC (PTree.Node111 l x2 r) else CC (PTree.Node111 l x r)
  end
 | PTree.Node101 l1 r1, PTree.Node011 x2 r2 =>
   match combine_l l1, f None (Some x2), xcombine r1 r2 with
  | Unchanged, None, Same => Same1
  | Unchanged, None, Same1 => Same1
  | Unchanged, None, Same2 => CC (PTree.Node101 l1 r2)
  | Unchanged, None, CC0 => CC (PTree.Node100 l1)
  | Unchanged, None, CC r => CC (PTree.Node101 l1 r)
  | Unchanged, Some x, Same => if L.beq x x2 then CC (PTree.Node111 l1 x2 r2) else CC (PTree.Node111 l1 x r2)
  | Unchanged, Some x, Same1 => if L.beq x x2 then CC (PTree.Node111 l1 x2 r1) else CC (PTree.Node111 l1 x r1)
  | Unchanged, Some x, Same2 => if L.beq x x2 then CC (PTree.Node111 l1 x2 r2) else CC (PTree.Node111 l1 x r2)
  | Unchanged, Some x, CC0 => if L.beq x x2 then CC (PTree.Node110 l1 x2) else CC (PTree.Node110 l1 x)
  | Unchanged, Some x, CC r => if L.beq x x2 then CC (PTree.Node111 l1 x2 r) else CC (PTree.Node111 l1 x r)
  | Chempty, None, Same => CC (PTree.Node001 r2)
  | Chempty, None, Same1 => CC (PTree.Node001 r1)
  | Chempty, None, Same2 => CC (PTree.Node001 r2)
  | Chempty, None, CC0 => CC0
  | Chempty, None, CC r => CC (PTree.Node001 r)
  | Chempty, Some x, Same => if L.beq x x2 then CC (PTree.Node011 x2 r2) else CC (PTree.Node011 x r2)
  | Chempty, Some x, Same1 => if L.beq x x2 then CC (PTree.Node011 x2 r1) else CC (PTree.Node011 x r1)
  | Chempty, Some x, Same2 => if L.beq x x2 then Same2 else CC (PTree.Node011 x r2)
  | Chempty, Some x, CC0 => if L.beq x x2 then CC (PTree.Node010 x2) else CC (PTree.Node010 x)
  | Chempty, Some x, CC r =>  if L.beq x x2 then CC (PTree.Node011 x2 r) else CC (PTree.Node011 x r)
  | Changed l, None, Same => CC (PTree.Node101 l r2)
  | Changed l, None, Same1 => CC (PTree.Node101 l r1)
  | Changed l, None, Same2 => CC (PTree.Node101 l r2)
  | Changed l, None, CC0 => CC (PTree.Node100 l)
  | Changed l, None, CC r => CC (PTree.Node101 l r)
  | Changed l, Some x, Same => if L.beq x x2 then CC (PTree.Node111 l x2 r2) else CC (PTree.Node111 l x r2)
  | Changed l, Some x, Same1 => if L.beq x x2 then CC (PTree.Node111 l x2 r1) else CC (PTree.Node111 l x r1)
  | Changed l, Some x, Same2 => if L.beq x x2 then CC (PTree.Node111 l x2 r2) else CC (PTree.Node111 l x r2)
  | Changed l, Some x, CC0 => if L.beq x x2 then CC (PTree.Node110 l x2) else CC (PTree.Node110 l x)
  | Changed l, Some x, CC r => if L.beq x x2 then CC (PTree.Node111 l x2 r) else CC (PTree.Node111 l x r)
 end
 | PTree.Node101 l1 r1, PTree.Node100 l2 =>
  match xcombine l1 l2, combine_l r1 with
  | Same, Unchanged => Same1
  | Same, Chempty => CC (PTree.Node100 l1)
  | Same, Changed r => CC (PTree.Node101 l1 r)
  | Same1, Unchanged => Same1
  | Same1, Chempty => CC (PTree.Node100 l1)
  | Same1, Changed r => CC (PTree.Node101 l1 r)
  | Same2, Unchanged => CC (PTree.Node101 l2 r1)
  | Same2, Chempty => Same2
  | Same2, Changed r => CC (PTree.Node101 l2 r)
  | CC0, Unchanged => CC (PTree.Node001 r1)
  | CC0, Chempty => CC0
  | CC0, Changed r => CC (PTree.Node001 r)
  | CC l, Unchanged => CC (PTree.Node101 l r1)
  | CC l, Chempty => CC (PTree.Node100 l)
  | CC l, Changed r => CC (PTree.Node101 l r)
  end
 | PTree.Node101 l1 r1, PTree.Node101 l2 r2 =>
  match xcombine l1 l2, xcombine r1 r2 with
  | Same, Same => Same
  | Same, Same1 => Same1
  | Same, Same2 => Same2
  | Same, CC0 => CC (PTree.Node100 l1)
  | Same, CC r => CC (PTree.Node101 l1 r)
  | Same1, Same => Same1
  | Same1, Same1 => Same1
  | Same1, Same2 => CC (PTree.Node101 l1 r2)
  | Same1, CC0 => CC (PTree.Node100 l1)
  | Same1, CC r => CC (PTree.Node101 l1 r)
  | Same2, Same => Same2
  | Same2, Same1 => CC (PTree.Node101 l2 r1)
  | Same2, Same2 => Same2
  | Same2, CC0 => CC (PTree.Node100 l2)
  | Same2, CC r => CC (PTree.Node101 l2 r)
  | CC0, Same => CC (PTree.Node001 r1)
  | CC0, Same1 => CC (PTree.Node001 r1)
  | CC0, Same2 => CC (PTree.Node001 r2)
  | CC0, CC0 => CC0
  | CC0, CC r => CC (PTree.Node001 r)
  | CC l, Same => CC (PTree.Node101 l r1)
  | CC l, Same1 => CC (PTree.Node101 l r1)
  | CC l, Same2 => CC (PTree.Node101 l r2)
  | CC l, CC0 => CC (PTree.Node100 l)
  | CC l, CC r => CC (PTree.Node101 l r)
  end
 | PTree.Node101 l1 r1, PTree.Node110 l2 x2 =>
  match xcombine l1 l2, f None (Some x2), combine_l r1 with
  | Same, None, Unchanged => Same1
  | Same, None, Chempty => CC (PTree.Node100 l1)
  | Same, None, Changed r => CC (PTree.Node101 l1 r)
  | Same, Some x, Unchanged => if L.beq x x2 then CC (PTree.Node111 l1 x2 r1) else CC (PTree.Node111 l1 x r1)
  | Same, Some x, Chempty => if L.beq x x2 then CC (PTree.Node110 l1 x2) else CC (PTree.Node110 l1 x)
  | Same, Some x, Changed r => if L.beq x x2 then CC (PTree.Node111 l1 x2 r) else CC (PTree.Node111 l1 x r)
  | Same1, None, Unchanged => Same1
  | Same1, None, Chempty => CC (PTree.Node100 l1)
  | Same1, None, Changed r => CC (PTree.Node101 l1 r)
  | Same1, Some x, Unchanged => if L.beq x x2 then CC (PTree.Node111 l1 x2 r1) else CC (PTree.Node111 l1 x r1)
  | Same1, Some x, Chempty => if L.beq x x2 then CC (PTree.Node110 l1 x2) else CC (PTree.Node110 l1 x)
  | Same1, Some x, Changed r => if L.beq x x2 then CC (PTree.Node111 l1 x2 r) else CC (PTree.Node111 l1 x r)
  | Same2, None, Unchanged => CC (PTree.Node101 l2 r1)
  | Same2, None, Chempty => CC (PTree.Node100 l2)
  | Same2, None, Changed r => CC (PTree.Node101 l2 r)
  | Same2, Some x, Unchanged => if L.beq x x2 then CC (PTree.Node111 l2 x2 r1) else CC (PTree.Node111 l2 x r1)
  | Same2, Some x, Chempty => if L.beq x x2 then Same2 else CC (PTree.Node110 l2 x)
  | Same2, Some x, Changed r => if L.beq x x2 then CC (PTree.Node111 l2 x2 r) else CC (PTree.Node111 l2 x r)
  | CC0, None, Unchanged => CC (PTree.Node001 r1)
  | CC0, None, Chempty => CC0
  | CC0, None, Changed r => CC (PTree.Node001 r)
  | CC0, Some x, Unchanged => if L.beq x x2 then CC (PTree.Node011 x2 r1) else CC (PTree.Node011 x r1)
  | CC0, Some x, Chempty => if L.beq x x2 then CC (PTree.Node010 x2) else CC (PTree.Node010 x)
  | CC0, Some x, Changed r => if L.beq x x2 then CC (PTree.Node011 x2 r) else CC (PTree.Node011 x r)
  | CC l, None, Unchanged => CC (PTree.Node101 l r1)
  | CC l, None, Chempty => CC (PTree.Node100 l)
  | CC l, None, Changed r => CC (PTree.Node101 l r)
  | CC l, Some x, Unchanged => if L.beq x x2 then CC (PTree.Node111 l x2 r1) else CC (PTree.Node111 l x r1)
  | CC l, Some x, Chempty => if L.beq x x2 then CC (PTree.Node110 l x2) else CC (PTree.Node110 l x)
  | CC l, Some x, Changed r => if L.beq x x2 then CC (PTree.Node111 l x2 r) else CC (PTree.Node111 l x r)
  end
 | PTree.Node101 l1 r1, PTree.Node111 l2 x2 r2 =>
  match xcombine l1 l2, f None (Some x2), xcombine r1 r2 with
  | Same, None, Same => Same1
  | Same, None, Same1 => Same1
  | Same, None, Same2 => CC (PTree.Node101 l2 r2)
  | Same, None, CC0 => CC (PTree.Node100 l1)
  | Same, None, CC r => CC (PTree.Node101 l2 r)
  | Same, Some x, Same => if L.beq x x2 then Same2 else CC (PTree.Node111 l2 x r2)
  | Same, Some x, Same1 => if L.beq x x2 then CC (PTree.Node111 l1 x2 r1) else CC (PTree.Node111 l1 x r1)
  | Same, Some x, Same2 => if L.beq x x2 then Same2 else CC (PTree.Node111 l2 x r2)
  | Same, Some x, CC0 => if L.beq x x2 then CC (PTree.Node110 l2 x2) else CC (PTree.Node110 l2 x)
  | Same, Some x, CC r => if L.beq x x2 then CC (PTree.Node111 l2 x2 r) else CC (PTree.Node111 l2 x r)
  | Same1, None, Same => Same1
  | Same1, None, Same1 => Same1
  | Same1, None, Same2 => CC (PTree.Node101 l1 r2)
  | Same1, None, CC0 => CC (PTree.Node100 l1)
  | Same1, None, CC r => CC (PTree.Node101 l1 r)
  | Same1, Some x, Same => if L.beq x x2 then CC (PTree.Node111 l1 x2 r2) else CC (PTree.Node111 l1 x r2)
  | Same1, Some x, Same1 => if L.beq x x2 then CC (PTree.Node111 l1 x2 r1) else CC (PTree.Node111 l1 x r1)
  | Same1, Some x, Same2 => if L.beq x x2 then CC (PTree.Node111 l1 x2 r2) else CC (PTree.Node111 l1 x r2)
  | Same1, Some x, CC0 => if L.beq x x2 then CC (PTree.Node110 l1 x2) else CC (PTree.Node110 l1 x)
  | Same1, Some x, CC r => if L.beq x x2 then CC (PTree.Node111 l1 x2 r) else CC (PTree.Node111 l1 x r)
  | Same2, None, Same => CC (PTree.Node101 l2 r2)
  | Same2, None, Same1 => CC (PTree.Node101 l2 r1)
  | Same2, None, Same2 => CC (PTree.Node101 l2 r2)
  | Same2, None, CC0 =>CC (PTree.Node100 l2)
  | Same2, None, CC r => CC (PTree.Node101 l2 r)
  | Same2, Some x, Same => if L.beq x x2 then Same2 else CC (PTree.Node111 l2 x r2)
  | Same2, Some x, Same1 => if L.beq x x2 then CC (PTree.Node111 l2 x2 r1) else CC (PTree.Node111 l2 x r1)
  | Same2, Some x, Same2 => if L.beq x x2 then Same2 else CC (PTree.Node111 l2 x r2)
  | Same2, Some x, CC0 => if L.beq x x2 then CC (PTree.Node110 l2 x2) else CC (PTree.Node110 l2 x)
  | Same2, Some x, CC r => if L.beq x x2 then CC (PTree.Node111 l2 x2 r) else CC (PTree.Node111 l2 x r)
  | CC0, None, Same => CC (PTree.Node001 r2)
  | CC0, None, Same1 => CC (PTree.Node001 r1)
  | CC0, None, Same2 => CC (PTree.Node001 r2)
  | CC0, None, CC0 => CC0
  | CC0, None, CC r => CC (PTree.Node001 r)
  | CC0, Some x, Same => if L.beq x x2 then CC (PTree.Node011 x2 r2) else CC (PTree.Node011 x r2)
  | CC0, Some x, Same1 => if L.beq x x2 then CC (PTree.Node011 x2 r1) else CC (PTree.Node011 x r1)
  | CC0, Some x, Same2 => if L.beq x x2 then CC (PTree.Node011 x2 r2) else CC (PTree.Node011 x r2)
  | CC0, Some x, CC0 => if L.beq x x2 then CC (PTree.Node010 x2) else CC (PTree.Node010 x)
  | CC0, Some x, CC r => if L.beq x x2 then CC (PTree.Node011 x2 r) else CC (PTree.Node011 x r)
  | CC l, None, Same => CC (PTree.Node101 l r2)
  | CC l, None, Same1 => CC (PTree.Node101 l r1)
  | CC l, None, Same2 => CC (PTree.Node101 l r2)
  | CC l, None, CC0 => CC (PTree.Node100 l)
  | CC l, None, CC r => CC (PTree.Node101 l r)
  | CC l, Some x, Same => if L.beq x x2 then CC (PTree.Node111 l x2 r2) else CC (PTree.Node111 l x r2)
  | CC l, Some x, Same1 => if L.beq x x2 then CC (PTree.Node111 l x2 r1) else CC (PTree.Node111 l x r1)
  | CC l, Some x, Same2 => if L.beq x x2 then CC (PTree.Node111 l x2 r2) else CC (PTree.Node111 l x r2)
  | CC l, Some x, CC0 => if L.beq x x2 then CC (PTree.Node110 l x2) else CC (PTree.Node110 l x)
  | CC l, Some x, CC r => if L.beq x x2 then CC (PTree.Node111 l x2 r) else CC (PTree.Node111 l x r)
  end
 | PTree.Node110 l1 x1, PTree.Node001 r2 =>
  match combine_l l1, f (Some x1) None, combine_r r2 with
  | Unchanged, None, Unchanged => CC (PTree.Node101 l1 r2)
  | Unchanged, None, Chempty => CC (PTree.Node100 l1)
  | Unchanged, None, Changed r => CC (PTree.Node101 l1 r)
  | Unchanged, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node111 l1 x1 r2) else CC (PTree.Node111 l1 x r2)
  | Unchanged, Some x, Chempty => if L.beq x x1 then Same1 else CC (PTree.Node110 l1 x)
  | Unchanged, Some x, Changed r => if L.beq x x1 then CC (PTree.Node111 l1 x1 r) else CC (PTree.Node111 l1 x r)
  | Chempty, None, Unchanged => Same2
  | Chempty, None, Chempty => CC0
  | Chempty, None, Changed r => CC (PTree.Node001 r)
  | Chempty, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node011 x1 r2) else CC (PTree.Node011 x r2)
  | Chempty, Some x, Chempty => if L.beq x x1 then CC (PTree.Node010 x1) else CC (PTree.Node010 x)
  | Chempty, Some x, Changed r => if L.beq x x1 then CC (PTree.Node011 x1 r) else CC (PTree.Node011 x r)
  | Changed l, None, Unchanged => CC (PTree.Node101 l r2)
  | Changed l, None, Chempty => CC (PTree.Node100 l)
  | Changed l, None, Changed r => CC (PTree.Node101 l r)
  | Changed l, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node111 l x1 r2) else CC (PTree.Node111 l x r2)
  | Changed l, Some x, Chempty => if L.beq x x1 then CC (PTree.Node110 l x1) else CC (PTree.Node110 l x)
  | Changed l, Some x, Changed r => if L.beq x x1 then CC (PTree.Node111 l x1 r) else CC (PTree.Node111 l x r)
  end
 | PTree.Node110 l1 x1, PTree.Node010 x2 =>
  match combine_l l1, f (Some x1) (Some x2) with
  | Unchanged, None => CC (PTree.Node100 l1)
  | Unchanged, Some x => if L.beq x x1 then Same1 else if L.beq x x2 then CC (PTree.Node110 l1 x2) else CC (PTree.Node110 l1 x)
  | Chempty, None => CC0
  | Chempty, Some x => if L.beq x x1 then CC (PTree.Node010 x1) else if L.beq x x2 then Same2 else CC (PTree.Node010 x)
  | Changed l, None => CC (PTree.Node100 l)
  | Changed l, Some x => if L.beq x x1 then CC (PTree.Node110 l x1) else if L.beq x x2 then CC (PTree.Node110 l x2) else CC (PTree.Node110 l x)
  end
 | PTree.Node110 l1 x1, PTree.Node011 x2 r2 =>
  match combine_l l1, f (Some x1) (Some x2), combine_r r2 with
  | Unchanged, None, Unchanged => CC (PTree.Node101 l1 r2)
  | Unchanged, None, Chempty => CC (PTree.Node100 l1)
  | Unchanged, None, Changed r => CC (PTree.Node101 l1 r)
  | Unchanged, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node111 l1 x1 r2) else if L.beq x x2 then CC (PTree.Node111 l1 x2 r2) else CC (PTree.Node111 l1 x r2)
  | Unchanged, Some x, Chempty => if L.beq x x1 then Same1 else if L.beq x x2 then CC (PTree.Node110 l1 x2) else CC (PTree.Node110 l1 x)
  | Unchanged, Some x, Changed r => if L.beq x x1 then CC (PTree.Node111 l1 x1 r) else if L.beq x x2 then CC (PTree.Node111 l1 x2 r) else CC (PTree.Node111 l1 x r)
  | Chempty, None, Unchanged => CC (PTree.Node001 r2)
  | Chempty, None, Chempty => CC0
  | Chempty, None, Changed r => CC (PTree.Node001 r)
  | Chempty, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node011 x1 r2) else if L.beq x x2 then Same2 else CC (PTree.Node011 x r2)
  | Chempty, Some x, Chempty => if L.beq x x1 then CC (PTree.Node010 x1) else if L.beq x x2 then CC (PTree.Node010 x2) else CC (PTree.Node010 x)
  | Chempty, Some x, Changed r => if L.beq x x1 then CC (PTree.Node011 x1 r) else if L.beq x x2 then CC (PTree.Node011 x2 r) else  CC (PTree.Node011 x r)
  | Changed l, None, Unchanged => CC (PTree.Node101 l r2)
  | Changed l, None, Chempty => CC (PTree.Node100 l)
  | Changed l, None, Changed r => CC (PTree.Node101 l r)
  | Changed l, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node111 l x1 r2) else if L.beq x x2 then CC (PTree.Node111 l x2 r2) else CC (PTree.Node111 l x r2)
  | Changed l, Some x, Chempty => if L.beq x x1 then CC (PTree.Node110 l x1) else if L.beq x x2 then CC (PTree.Node110 l x2) else CC (PTree.Node110 l x)
  | Changed l, Some x, Changed r => if L.beq x x1 then CC (PTree.Node111 l x1 r) else if L.beq x x2 then CC (PTree.Node111 l x2 r) else CC (PTree.Node111 l x r)
  end
 | PTree.Node110 l1 x1, PTree.Node100 l2 =>
  match xcombine l1 l2, f (Some x1) None with
  | Same, None => Same2
  | Same, Some x => if L.beq x x1 then Same1 else CC (PTree.Node110 l1 x)
  | Same1, None => CC (PTree.Node100 l1)
  | Same1, Some x => if L.beq x x1 then Same1 else CC (PTree.Node110 l1 x)
  | Same2, None => Same2
  | Same2, Some x => if L.beq x x1 then CC (PTree.Node110 l2 x1) else CC (PTree.Node110 l2 x)
  | CC0, None => CC0
  | CC0, Some x => if L.beq x x1 then CC (PTree.Node010 x1) else CC (PTree.Node010 x)
  | CC l, None => CC (PTree.Node100 l)
  | CC l, Some x => if L.beq x x1 then CC (PTree.Node110 l x1) else CC (PTree.Node110 l x)
  end
 | PTree.Node110 l1 x1, PTree.Node101 l2 r2 => 
  match xcombine l1 l2, f (Some x1) None, combine_r r2 with
  | Same, None, Unchanged => Same2
  | Same, None, Chempty => CC (PTree.Node100 l1)
  | Same, None, Changed r => CC (PTree.Node101 l1 r)
  | Same, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node111 l1 x1 r2) else CC (PTree.Node111 l1 x r2)
  | Same, Some x, Chempty => if L.beq x x1 then Same1 else CC (PTree.Node110 l1 x)
  | Same, Some x, Changed r => if L.beq x x1 then CC (PTree.Node111 l1 x1 r) else CC (PTree.Node111 l1 x r)
  | Same1, None, Unchanged => CC (PTree.Node101 l1 r2)
  | Same1, None, Chempty => CC (PTree.Node100 l1)
  | Same1, None, Changed r => CC (PTree.Node101 l1 r)
  | Same1, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node111 l1 x1 r2) else CC (PTree.Node111 l1 x r2)
  | Same1, Some x, Chempty => if L.beq x x1 then Same1 else CC (PTree.Node110 l1 x)
  | Same1, Some x, Changed r => if L.beq x x1 then CC (PTree.Node111 l1 x1 r) else CC (PTree.Node111 l1 x r)
  | Same2, None, Unchanged => Same2
  | Same2, None, Chempty => CC (PTree.Node100 l2)
  | Same2, None, Changed r => CC (PTree.Node101 l2 r)
  | Same2, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node111 l2 x1 r2) else CC (PTree.Node111 l2 x r2)
  | Same2, Some x, Chempty => if L.beq x x1 then CC (PTree.Node110 l2 x1) else CC (PTree.Node110 l2 x)
  | Same2, Some x, Changed r => if L.beq x x1 then CC (PTree.Node111 l2 x1 r) else CC (PTree.Node111 l2 x r)
  | CC0, None, Unchanged => CC (PTree.Node001 r2)
  | CC0, None, Chempty => CC0
  | CC0, None, Changed r => CC (PTree.Node001 r)
  | CC0, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node011 x1 r2) else CC (PTree.Node011 x r2)
  | CC0, Some x, Chempty => if L.beq x x1 then CC (PTree.Node010 x1) else CC (PTree.Node010 x)
  | CC0, Some x, Changed r => if L.beq x x1 then CC (PTree.Node011 x1 r) else CC (PTree.Node011 x r)
  | CC l, None, Unchanged => CC (PTree.Node101 l r2)
  | CC l, None, Chempty => CC (PTree.Node100 l)
  | CC l, None, Changed r => CC (PTree.Node101 l r)
  | CC l, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node111 l x1 r2) else CC (PTree.Node111 l x r2)
  | CC l, Some x, Chempty => if L.beq x x1 then CC (PTree.Node110 l x1) else CC (PTree.Node110 l x)
  | CC l, Some x, Changed r => if L.beq x x1 then CC (PTree.Node111 l x1 r) else CC (PTree.Node111 l x r)
  end
 | PTree.Node110 l1 x1, PTree.Node110 l2 x2 =>
  match xcombine l1 l2, f (Some x1) (Some x2) with
  | Same, None => CC (PTree.Node100 l1)
  | Same, Some x => if L.beq x x1 then Same1 else if L.beq x x2 then Same2 else CC (PTree.Node110 l1 x)
  | Same1, None => CC (PTree.Node100 l1)
  | Same1, Some x => if L.beq x x1 then Same1 else if L.beq x x2 then CC (PTree.Node110 l1 x2) else CC (PTree.Node110 l1 x)
  | Same2, None => CC (PTree.Node100 l2)
  | Same2, Some x => if L.beq x x1 then CC (PTree.Node110 l2 x1) else if L.beq x x2 then Same2 else CC (PTree.Node110 l2 x)
  | CC0, None => CC0
  | CC0, Some x => if L.beq x x1 then CC (PTree.Node010 x1) else if L.beq x x2 then CC (PTree.Node010 x2) else CC (PTree.Node010 x)
  | CC l, None => CC (PTree.Node100 l)
  | CC l, Some x => if L.beq x x1 then CC (PTree.Node110 l x1) else if L.beq x x2 then CC (PTree.Node110 l x2) else CC (PTree.Node110 l x)
  end
 | PTree.Node110 l1 x1, PTree.Node111 l2 x2 r2 =>
  match xcombine l1 l2, f (Some x1) (Some x2), combine_r r2 with
  | Same, None, Unchanged => CC (PTree.Node101 l2 r2)
  | Same, None, Chempty => CC (PTree.Node100 l1)
  | Same, None, Changed r => CC (PTree.Node101 l1 r)
  | Same, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node111 l1 x1 r2) else if L.beq x x2 then Same2 else CC (PTree.Node111 l1 x r2)
  | Same, Some x, Chempty => if L.beq x x1 then Same1 else if L.beq x x2 then CC (PTree.Node110 l1 x2) else CC (PTree.Node110 l1 x)
  | Same, Some x, Changed r => if L.beq x x1 then CC (PTree.Node111 l1 x1 r) else if L.beq x x2 then CC (PTree.Node111 l1 x2 r) else CC (PTree.Node111 l1 x r)
  | Same1, None, Unchanged => CC (PTree.Node101 l1 r2)
  | Same1, None, Chempty => CC (PTree.Node100 l1)
  | Same1, None, Changed r => CC (PTree.Node101 l1 r)
  | Same1, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node111 l1 x1 r2) else if L.beq x x2 then CC (PTree.Node111 l1 x2 r2) else CC (PTree.Node111 l1 x r2)
  | Same1, Some x, Chempty => if L.beq x x1 then Same1 else if L.beq x x2 then CC (PTree.Node110 l1 x2) else CC (PTree.Node110 l1 x)
  | Same1, Some x, Changed r => if L.beq x x1 then CC (PTree.Node111 l1 x1 r) else if L.beq x x2 then CC (PTree.Node111 l1 x2 r) else CC (PTree.Node111 l1 x r)
  | Same2, None, Unchanged => CC (PTree.Node101 l2 r2)
  | Same2, None, Chempty => CC (PTree.Node100 l2)
  | Same2, None, Changed r => CC (PTree.Node101 l2 r)
  | Same2, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node111 l2 x1 r2) else if L.beq x x2 then Same2 else CC (PTree.Node111 l2 x r2)
  | Same2, Some x, Chempty => if L.beq x x1 then CC (PTree.Node110 l2 x1) else if L.beq x x2 then CC (PTree.Node110 l2 x2) else CC (PTree.Node110 l2 x)
  | Same2, Some x, Changed r => if L.beq x x1 then CC (PTree.Node111 l2 x1 r) else if L.beq x x2 then CC (PTree.Node111 l2 x2 r) else CC (PTree.Node111 l2 x r)
  | CC0, None, Unchanged => CC (PTree.Node001 r2)
  | CC0, None, Chempty => CC0
  | CC0, None, Changed r => CC (PTree.Node001 r)
  | CC0, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node011 x1 r2) else if L.beq x x2 then CC (PTree.Node011 x2 r2) else CC (PTree.Node011 x r2)
  | CC0, Some x, Chempty => if L.beq x x1 then CC (PTree.Node010 x1) else if L.beq x x2 then CC (PTree.Node010 x2) else CC (PTree.Node010 x)
  | CC0, Some x, Changed r => if L.beq x x1 then CC (PTree.Node011 x1 r) else if L.beq x x2 then CC (PTree.Node011 x2 r) else CC (PTree.Node011 x r)
  | CC l, None, Unchanged => CC (PTree.Node101 l r2)
  | CC l, None, Chempty => CC (PTree.Node100 l)
  | CC l, None, Changed r => CC (PTree.Node101 l r)
  | CC l, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node111 l x1 r2) else if L.beq x x2 then CC (PTree.Node111 l x2 r2) else CC (PTree.Node111 l x r2)
  | CC l, Some x, Chempty => if L.beq x x1 then CC (PTree.Node110 l x1) else if L.beq x x2 then CC (PTree.Node110 l x2) else CC (PTree.Node110 l x)
  | CC l, Some x, Changed r => if L.beq x x1 then CC (PTree.Node111 l x1 r) else if L.beq x x2 then CC (PTree.Node111 l x2 r) else CC (PTree.Node111 l x r)
  end
 | PTree.Node111 l1 x1 r1, PTree.Node001 r2 =>
  match combine_l l1, f (Some x1) None, xcombine r1 r2 with
  | Unchanged, None, Same => CC (PTree.Node101 l1 r1)
  | Unchanged, None, Same1 => CC (PTree.Node101 l1 r1)
  | Unchanged, None, Same2 => CC (PTree.Node101 l1 r2)
  | Unchanged, None, CC0 => CC (PTree.Node100 l1)
  | Unchanged, None, CC r => CC (PTree.Node101 l1 r)
  | Unchanged, Some x, Same => if L.beq x x1 then Same1 else CC (PTree.Node111 l1 x r1)
  | Unchanged, Some x, Same1 => if L.beq x x1 then Same1 else CC (PTree.Node111 l1 x r1)
  | Unchanged, Some x, Same2 => if L.beq x x1 then CC (PTree.Node111 l1 x1 r2) else CC (PTree.Node111 l1 x r2)
  | Unchanged, Some x, CC0 => if L.beq x x1 then CC (PTree.Node110 l1 x1) else CC (PTree.Node110 l1 x)
  | Unchanged, Some x, CC r => if L.beq x x1 then CC (PTree.Node111 l1 x1 r) else CC (PTree.Node111 l1 x r)
  | Chempty, None, Same => Same2
  | Chempty, None, Same1 => CC (PTree.Node001 r1)
  | Chempty, None, Same2 => Same2
  | Chempty, None, CC0 => CC0
  | Chempty, None, CC r => CC (PTree.Node001 r)
  | Chempty, Some x, Same => if L.beq x x1 then CC (PTree.Node011 x1 r2) else CC (PTree.Node011 x r2)
  | Chempty, Some x, Same1 => if L.beq x x1 then CC (PTree.Node011 x1 r1) else CC (PTree.Node011 x r1)
  | Chempty, Some x, Same2 => if L.beq x x1 then CC (PTree.Node011 x1 r2) else CC (PTree.Node011 x r2)
  | Chempty, Some x, CC0 => if L.beq x x1 then CC (PTree.Node010 x1) else CC (PTree.Node010 x)
  | Chempty, Some x, CC r =>  if L.beq x x1 then CC (PTree.Node011 x1 r) else CC (PTree.Node011 x r)
  | Changed l, None, Same => CC (PTree.Node101 l r2)
  | Changed l, None, Same1 => CC (PTree.Node101 l r1)
  | Changed l, None, Same2 => CC (PTree.Node101 l r2)
  | Changed l, None, CC0 => CC (PTree.Node100 l)
  | Changed l, None, CC r => CC (PTree.Node101 l r)
  | Changed l, Some x, Same => if L.beq x x1 then CC (PTree.Node111 l x1 r2) else CC (PTree.Node111 l x r2)
  | Changed l, Some x, Same1 => if L.beq x x1 then CC (PTree.Node111 l x1 r1) else CC (PTree.Node111 l x r1)
  | Changed l, Some x, Same2 => if L.beq x x1 then CC (PTree.Node111 l x1 r2) else CC (PTree.Node111 l x r2)
  | Changed l, Some x, CC0 => if L.beq x x1 then CC (PTree.Node110 l x1) else CC (PTree.Node110 l x)
  | Changed l, Some x, CC r => if L.beq x x1 then CC (PTree.Node111 l x1 r) else CC (PTree.Node111 l x r)
 end
 | PTree.Node111 l1 x1 r1, PTree.Node010 x2 =>
  match combine_l l1, f (Some x1) (Some x2), combine_l r1 with
  | Unchanged, None, Unchanged => CC (PTree.Node101 l1 r1)
  | Unchanged, None, Chempty => CC (PTree.Node100 l1)
  | Unchanged, None, Changed r => CC (PTree.Node101 l1 r)
  | Unchanged, Some x, Unchanged => if L.beq x x1 then Same1 else if L.beq x x2 then CC (PTree.Node111 l1 x2 r1) else CC (PTree.Node111 l1 x r1)
  | Unchanged, Some x, Chempty => if L.beq x x1 then CC (PTree.Node110 l1 x1) else if L.beq x x2 then CC (PTree.Node110 l1 x2) else CC (PTree.Node110 l1 x)
  | Unchanged, Some x, Changed r => if L.beq x x1 then CC (PTree.Node111 l1 x1 r) else if L.beq x x2 then CC (PTree.Node111 l1 x2 r) else CC (PTree.Node111 l1 x r)
  | Chempty, None, Unchanged => CC (PTree.Node001 r1)
  | Chempty, None, Chempty => CC0
  | Chempty, None, Changed r => CC (PTree.Node001 r)
  | Chempty, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node011 x1 r1) else if L.beq x x2 then CC (PTree.Node011 x2 r1) else CC (PTree.Node011 x r1)
  | Chempty, Some x, Chempty => if L.beq x x2 then Same2 else CC (PTree.Node010 x)
  | Chempty, Some x, Changed r => if L.beq x x1 then CC (PTree.Node011 x1 r) else if L.beq x x2 then CC (PTree.Node011 x2 r) else CC (PTree.Node011 x r)
  | Changed l, None, Unchanged => CC (PTree.Node101 l r1)
  | Changed l, None, Chempty => CC (PTree.Node100 l)
  | Changed l, None, Changed r => CC (PTree.Node101 l r)
  | Changed l, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node111 l x1 r1) else if L.beq x x2 then CC (PTree.Node111 l x2 r1) else CC (PTree.Node111 l x r1)
  | Changed l, Some x, Chempty => if L.beq x x1 then CC (PTree.Node110 l x1) else if L.beq x x2 then CC (PTree.Node110 l x2) else CC (PTree.Node110 l x)
  | Changed l, Some x, Changed r => if L.beq x x1 then CC (PTree.Node111 l x1 r) else if L.beq x x2 then CC (PTree.Node111 l x2 r) else CC (PTree.Node111 l x r)
  end
 | PTree.Node111 l1 x1 r1, PTree.Node011 x2 r2 =>
  match combine_l l1, f (Some x1) (Some x2), xcombine r1 r2 with
  | Unchanged, None, Same => CC (PTree.Node101 l1 r1)
  | Unchanged, None, Same1 => CC (PTree.Node101 l1 r1)
  | Unchanged, None, Same2 => CC (PTree.Node101 l1 r2)
  | Unchanged, None, CC0 => CC (PTree.Node100 l1)
  | Unchanged, None, CC r => CC (PTree.Node101 l1 r)
  | Unchanged, Some x, Same => if L.beq x x1 then Same1 else if L.beq x x2 then CC (PTree.Node111 l1 x2 r2) else CC (PTree.Node111 l1 x r1)
  | Unchanged, Some x, Same1 => if L.beq x x1 then Same1 else if L.beq x x2 then CC (PTree.Node111 l1 x2 r1) else CC (PTree.Node111 l1 x r1)
  | Unchanged, Some x, Same2 => if L.beq x x1 then CC (PTree.Node111 l1 x1 r2) else if L.beq x x2 then CC (PTree.Node111 l1 x2 r2) else CC (PTree.Node111 l1 x r2)
  | Unchanged, Some x, CC0 => if L.beq x x1 then CC (PTree.Node110 l1 x1) else if L.beq x x2 then CC (PTree.Node110 l1 x2) else CC (PTree.Node110 l1 x)
  | Unchanged, Some x, CC r => if L.beq x x1 then CC (PTree.Node111 l1 x1 r) else if L.beq x x2 then CC (PTree.Node111 l1 x2 r) else CC (PTree.Node111 l1 x r)
  | Chempty, None, Same => CC (PTree.Node001 r2)
  | Chempty, None, Same1 => CC (PTree.Node001 r1)
  | Chempty, None, Same2 => CC (PTree.Node001 r2)
  | Chempty, None, CC0 => CC0
  | Chempty, None, CC r => CC (PTree.Node001 r)
  | Chempty, Some x, Same => if L.beq x x1 then CC (PTree.Node011 x1 r2) else if L.beq x x2 then Same2 else CC (PTree.Node011 x r2)
  | Chempty, Some x, Same1 => if L.beq x x1 then CC (PTree.Node011 x1 r1) else if L.beq x x2 then CC (PTree.Node011 x2 r1) else CC (PTree.Node011 x r1)
  | Chempty, Some x, Same2 => if L.beq x x1 then CC (PTree.Node011 x1 r2) else if L.beq x x2 then Same2 else CC (PTree.Node011 x r2)
  | Chempty, Some x, CC0 => if L.beq x x1 then CC (PTree.Node010 x1) else if L.beq x x2 then CC (PTree.Node010 x2) else CC (PTree.Node010 x)
  | Chempty, Some x, CC r =>  if L.beq x x1 then CC (PTree.Node011 x1 r) else if L.beq x x2 then CC (PTree.Node011 x2 r) else CC (PTree.Node011 x r)
  | Changed l, None, Same => CC (PTree.Node101 l r2)
  | Changed l, None, Same1 => CC (PTree.Node101 l r1)
  | Changed l, None, Same2 => CC (PTree.Node101 l r2)
  | Changed l, None, CC0 => CC (PTree.Node100 l)
  | Changed l, None, CC r => CC (PTree.Node101 l r)
  | Changed l, Some x, Same => if L.beq x x1 then CC (PTree.Node111 l x1 r2) else if L.beq x x2 then CC (PTree.Node111 l x2 r2) else CC (PTree.Node111 l x r2)
  | Changed l, Some x, Same1 => if L.beq x x1 then CC (PTree.Node111 l x1 r1) else if L.beq x x2 then CC (PTree.Node111 l x2 r1) else CC (PTree.Node111 l x r1)
  | Changed l, Some x, Same2 => if L.beq x x1 then CC (PTree.Node111 l x1 r2) else if L.beq x x2 then CC (PTree.Node111 l x2 r2) else CC (PTree.Node111 l x r2)
  | Changed l, Some x, CC0 => if L.beq x x1 then CC (PTree.Node110 l x1) else if L.beq x x2 then CC (PTree.Node110 l x2) else CC (PTree.Node110 l x)
  | Changed l, Some x, CC r => if L.beq x x1 then CC (PTree.Node111 l x1 r) else if L.beq x x2 then CC (PTree.Node111 l x2 r) else CC (PTree.Node111 l x r)
 end
 | PTree.Node111 l1 x1 r1, PTree.Node100 l2 =>
  match xcombine l1 l2, f (Some x1) None, combine_l r1 with
  | Same, None, Unchanged => CC (PTree.Node101 l1 r1)
  | Same, None, Chempty => CC (PTree.Node100 l1)
  | Same, None, Changed r => CC (PTree.Node101 l1 r)
  | Same, Some x, Unchanged => if L.beq x x1 then Same1 else CC (PTree.Node111 l1 x r1)
  | Same, Some x, Chempty => if L.beq x x1 then CC (PTree.Node110 l1 x1) else CC (PTree.Node110 l1 x)
  | Same, Some x, Changed r => if L.beq x x1 then CC (PTree.Node111 l1 x1 r) else CC (PTree.Node111 l1 x r)
  | Same1, None, Unchanged => CC (PTree.Node101 l1 r1)
  | Same1, None, Chempty => CC (PTree.Node100 l1)
  | Same1, None, Changed r => CC (PTree.Node101 l1 r)
  | Same1, Some x, Unchanged => if L.beq x x1 then Same1 else CC (PTree.Node111 l1 x r1)
  | Same1, Some x, Chempty => if L.beq x x1 then CC (PTree.Node110 l1 x1) else CC (PTree.Node110 l1 x)
  | Same1, Some x, Changed r => if L.beq x x1 then CC (PTree.Node111 l1 x1 r) else CC (PTree.Node111 l1 x r)
  | Same2, None, Unchanged => CC (PTree.Node101 l2 r1)
  | Same2, None, Chempty => CC (PTree.Node100 l2)
  | Same2, None, Changed r => CC (PTree.Node101 l2 r)
  | Same2, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node111 l2 x1 r1) else CC (PTree.Node111 l2 x r1)
  | Same2, Some x, Chempty => if L.beq x x1 then CC (PTree.Node110 l2 x1) else CC (PTree.Node110 l2 x)
  | Same2, Some x, Changed r => if L.beq x x1 then CC (PTree.Node111 l2 x1 r) else CC (PTree.Node111 l2 x r)
  | CC0, None, Unchanged => CC (PTree.Node001 r1)
  | CC0, None, Chempty => CC0
  | CC0, None, Changed r => CC (PTree.Node001 r)
  | CC0, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node011 x1 r1) else CC (PTree.Node011 x r1)
  | CC0, Some x, Chempty => if L.beq x x1 then CC (PTree.Node010 x1) else CC (PTree.Node010 x)
  | CC0, Some x, Changed r => if L.beq x x1 then CC (PTree.Node011 x1 r) else CC (PTree.Node011 x r)
  | CC l, None, Unchanged => CC (PTree.Node101 l r1)
  | CC l, None, Chempty => CC (PTree.Node100 l)
  | CC l, None, Changed r => CC (PTree.Node101 l r)
  | CC l, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node111 l x1 r1) else CC (PTree.Node111 l x r1)
  | CC l, Some x, Chempty => if L.beq x x1 then CC (PTree.Node110 l x1) else CC (PTree.Node110 l x)
  | CC l, Some x, Changed r => if L.beq x x1 then CC (PTree.Node111 l x1 r) else CC (PTree.Node111 l x r)
  end
 | PTree.Node111 l1 x1 r1, PTree.Node101 l2 r2 =>
  match xcombine l1 l2, f (Some x1) None, xcombine r1 r2 with
  | Same, None, Same => Same2
  | Same, None, Same1 => CC (PTree.Node101 l1 r1)
  | Same, None, Same2 => Same2
  | Same, None, CC0 => CC (PTree.Node100 l1)
  | Same, None, CC r => CC (PTree.Node101 l2 r)
  | Same, Some x, Same => if L.beq x x1 then Same1 else CC (PTree.Node111 l2 x r2)
  | Same, Some x, Same1 => if L.beq x x1 then Same1 else CC (PTree.Node111 l1 x r1)
  | Same, Some x, Same2 => if L.beq x x1 then CC (PTree.Node111 l2 x1 r2) else CC (PTree.Node111 l2 x r2)
  | Same, Some x, CC0 => if L.beq x x1 then CC (PTree.Node110 l2 x1) else CC (PTree.Node110 l2 x)
  | Same, Some x, CC r => if L.beq x x1 then CC (PTree.Node111 l2 x1 r) else CC (PTree.Node111 l2 x r)
  | Same1, None, Same => CC (PTree.Node101 l1 r1)
  | Same1, None, Same1 => CC (PTree.Node101 l1 r1)
  | Same1, None, Same2 => CC (PTree.Node101 l1 r2)
  | Same1, None, CC0 => CC (PTree.Node100 l1)
  | Same1, None, CC r => CC (PTree.Node101 l1 r)
  | Same1, Some x, Same => if L.beq x x1 then Same1 else CC (PTree.Node111 l1 x r2)
  | Same1, Some x, Same1 => if L.beq x x1 then Same1 else CC (PTree.Node111 l1 x r1)
  | Same1, Some x, Same2 => if L.beq x x1 then CC (PTree.Node111 l1 x1 r2) else CC (PTree.Node111 l1 x r2)
  | Same1, Some x, CC0 => if L.beq x x1 then CC (PTree.Node110 l1 x1) else CC (PTree.Node110 l1 x)
  | Same1, Some x, CC r => if L.beq x x1 then CC (PTree.Node111 l1 x1 r) else CC (PTree.Node111 l1 x r)
  | Same2, None, Same => CC (PTree.Node101 l2 r2)
  | Same2, None, Same1 => CC (PTree.Node101 l2 r1)
  | Same2, None, Same2 => CC (PTree.Node101 l2 r2)
  | Same2, None, CC0 =>CC (PTree.Node100 l2)
  | Same2, None, CC r => CC (PTree.Node101 l2 r)
  | Same2, Some x, Same => if L.beq x x1 then CC (PTree.Node111 l2 x1 r2) else CC (PTree.Node111 l2 x r2)
  | Same2, Some x, Same1 => if L.beq x x1 then CC (PTree.Node111 l2 x1 r1) else CC (PTree.Node111 l2 x r1)
  | Same2, Some x, Same2 => if L.beq x x1 then CC (PTree.Node111 l2 x1 r2) else CC (PTree.Node111 l2 x r2)
  | Same2, Some x, CC0 => if L.beq x x1 then CC (PTree.Node110 l2 x1) else CC (PTree.Node110 l2 x)
  | Same2, Some x, CC r => if L.beq x x1 then CC (PTree.Node111 l2 x1 r) else CC (PTree.Node111 l2 x r)
  | CC0, None, Same => CC (PTree.Node001 r2)
  | CC0, None, Same1 => CC (PTree.Node001 r1)
  | CC0, None, Same2 => CC (PTree.Node001 r2)
  | CC0, None, CC0 => CC0
  | CC0, None, CC r => CC (PTree.Node001 r)
  | CC0, Some x, Same => if L.beq x x1 then CC (PTree.Node011 x1 r2) else CC (PTree.Node011 x r2)
  | CC0, Some x, Same1 => if L.beq x x1 then CC (PTree.Node011 x1 r1) else CC (PTree.Node011 x r1)
  | CC0, Some x, Same2 => if L.beq x x1 then CC (PTree.Node011 x1 r2) else CC (PTree.Node011 x r2)
  | CC0, Some x, CC0 => if L.beq x x1 then CC (PTree.Node010 x1) else CC (PTree.Node010 x)
  | CC0, Some x, CC r => if L.beq x x1 then CC (PTree.Node011 x1 r) else CC (PTree.Node011 x r)
  | CC l, None, Same => CC (PTree.Node101 l r2)
  | CC l, None, Same1 => CC (PTree.Node101 l r1)
  | CC l, None, Same2 => CC (PTree.Node101 l r2)
  | CC l, None, CC0 => CC (PTree.Node100 l)
  | CC l, None, CC r => CC (PTree.Node101 l r)
  | CC l, Some x, Same => if L.beq x x1 then CC (PTree.Node111 l x1 r2) else CC (PTree.Node111 l x r2)
  | CC l, Some x, Same1 => if L.beq x x1 then CC (PTree.Node111 l x1 r1) else CC (PTree.Node111 l x r1)
  | CC l, Some x, Same2 => if L.beq x x1 then CC (PTree.Node111 l x1 r2) else CC (PTree.Node111 l x r2)
  | CC l, Some x, CC0 => if L.beq x x1 then CC (PTree.Node110 l x1) else CC (PTree.Node110 l x)
  | CC l, Some x, CC r => if L.beq x x1 then CC (PTree.Node111 l x1 r) else CC (PTree.Node111 l x r)
  end
 | PTree.Node111 l1 x1 r1, PTree.Node110 l2 x2 =>
  match xcombine l1 l2, f (Some x1) (Some x2), combine_l r1 with
  | Same, None, Unchanged => CC (PTree.Node101 l1 r1)
  | Same, None, Chempty => CC (PTree.Node100 l1)
  | Same, None, Changed r => CC (PTree.Node101 l1 r)
  | Same, Some x, Unchanged => if L.beq x x1 then Same1 else if L.beq x x2 then CC (PTree.Node111 l1 x2 r1) else CC (PTree.Node111 l1 x r1)
  | Same, Some x, Chempty => if L.beq x x1 then CC (PTree.Node110 l1 x1) else if L.beq x x2 then Same2 else CC (PTree.Node110 l1 x)
  | Same, Some x, Changed r => if L.beq x x1 then CC (PTree.Node111 l1 x1 r) else if L.beq x x2 then CC (PTree.Node111 l1 x2 r) else CC (PTree.Node111 l1 x r)
  | Same1, None, Unchanged => CC (PTree.Node101 l1 r1)
  | Same1, None, Chempty => CC (PTree.Node100 l1)
  | Same1, None, Changed r => CC (PTree.Node101 l1 r)
  | Same1, Some x, Unchanged => if L.beq x x1 then Same1 else if L.beq x x2 then CC (PTree.Node111 l1 x2 r1) else CC (PTree.Node111 l1 x r1)
  | Same1, Some x, Chempty => if L.beq x x1 then CC (PTree.Node110 l1 x1) else if L.beq x x2 then CC (PTree.Node110 l1 x2) else CC (PTree.Node110 l1 x)
  | Same1, Some x, Changed r => if L.beq x x1 then CC (PTree.Node111 l1 x1 r) else if L.beq x x2 then CC (PTree.Node111 l1 x2 r) else CC (PTree.Node111 l1 x r)
  | Same2, None, Unchanged => CC (PTree.Node101 l2 r1)
  | Same2, None, Chempty => CC (PTree.Node100 l2)
  | Same2, None, Changed r => CC (PTree.Node101 l2 r)
  | Same2, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node111 l2 x1 r1) else if L.beq x x2 then CC (PTree.Node111 l2 x2 r1) else CC (PTree.Node111 l2 x r1)
  | Same2, Some x, Chempty => if L.beq x x1 then CC (PTree.Node110 l2 x1) else if L.beq x x2 then Same2 else CC (PTree.Node110 l2 x)
  | Same2, Some x, Changed r => if L.beq x x1 then CC (PTree.Node111 l2 x1 r) else if L.beq x x2 then CC (PTree.Node111 l2 x2 r) else CC (PTree.Node111 l2 x r)
  | CC0, None, Unchanged => CC (PTree.Node001 r1)
  | CC0, None, Chempty => CC0
  | CC0, None, Changed r => CC (PTree.Node001 r)
  | CC0, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node011 x1 r1) else if L.beq x x2 then CC (PTree.Node011 x2 r1) else CC (PTree.Node011 x r1)
  | CC0, Some x, Chempty => if L.beq x x1 then CC (PTree.Node010 x1) else if L.beq x x2 then CC (PTree.Node010 x2) else CC (PTree.Node010 x)
  | CC0, Some x, Changed r => if L.beq x x1 then CC (PTree.Node011 x1 r) else if L.beq x x2 then CC (PTree.Node011 x2 r) else CC (PTree.Node011 x r)
  | CC l, None, Unchanged => CC (PTree.Node101 l r1)
  | CC l, None, Chempty => CC (PTree.Node100 l)
  | CC l, None, Changed r => CC (PTree.Node101 l r)
  | CC l, Some x, Unchanged => if L.beq x x1 then CC (PTree.Node111 l x1 r1) else if L.beq x x2 then CC (PTree.Node111 l x2 r1) else CC (PTree.Node111 l x r1)
  | CC l, Some x, Chempty => if L.beq x x1 then CC (PTree.Node110 l x1) else if L.beq x x2 then CC (PTree.Node110 l x2) else CC (PTree.Node110 l x)
  | CC l, Some x, Changed r => if L.beq x x1 then CC (PTree.Node111 l x1 r) else if L.beq x x2 then CC (PTree.Node111 l x2 r) else CC (PTree.Node111 l x r)
  end
 | PTree.Node111 l1 x1 r1, PTree.Node111 l2 x2 r2 =>
  match xcombine l1 l2, f (Some x1) (Some x2), xcombine r1 r2 with
  | Same, None, Same => CC (PTree.Node101 l1 r1)
  | Same, None, Same1 => CC (PTree.Node101 l1 r1)
  | Same, None, Same2 => CC (PTree.Node101 l2 r2)
  | Same, None, CC0 => CC (PTree.Node100 l1)
  | Same, None, CC r => CC (PTree.Node101 l2 r)
  | Same, Some x, Same => if L.beq x x1 then Same1 else if L.beq x x2 then Same2 else CC (PTree.Node111 l2 x r2)
  | Same, Some x, Same1 => if L.beq x x1 then Same1 else if L.beq x x2 then CC (PTree.Node111 l2 x2 r1) else CC (PTree.Node111 l1 x r1)
  | Same, Some x, Same2 => if L.beq x x1 then CC (PTree.Node111 l2 x1 r2) else if L.beq x x2 then Same2 else CC (PTree.Node111 l2 x r2)
  | Same, Some x, CC0 => if L.beq x x1 then CC (PTree.Node110 l2 x1) else if L.beq x x2 then CC (PTree.Node110 l2 x2) else CC (PTree.Node110 l2 x)
  | Same, Some x, CC r => if L.beq x x1 then CC (PTree.Node111 l2 x1 r) else if L.beq x x2 then CC (PTree.Node111 l2 x2 r) else CC (PTree.Node111 l2 x r)
  | Same1, None, Same => CC (PTree.Node101 l1 r1)
  | Same1, None, Same1 => CC (PTree.Node101 l1 r1)
  | Same1, None, Same2 => CC (PTree.Node101 l1 r2)
  | Same1, None, CC0 => CC (PTree.Node100 l1)
  | Same1, None, CC r => CC (PTree.Node101 l1 r)
  | Same1, Some x, Same => if L.beq x x1 then Same1 else if L.beq x x2 then CC (PTree.Node111 l1 x2 r2) else CC (PTree.Node111 l1 x r2)
  | Same1, Some x, Same1 => if L.beq x x1 then Same1 else if L.beq x x2 then CC (PTree.Node111 l1 x2 r1) else CC (PTree.Node111 l1 x r1)
  | Same1, Some x, Same2 => if L.beq x x1 then CC (PTree.Node111 l1 x1 r2) else if L.beq x x2 then CC (PTree.Node111 l1 x2 r2) else CC (PTree.Node111 l1 x r2)
  | Same1, Some x, CC0 => if L.beq x x1 then CC (PTree.Node110 l1 x1) else if L.beq x x2 then CC (PTree.Node110 l1 x2) else CC (PTree.Node110 l1 x)
  | Same1, Some x, CC r => if L.beq x x1 then CC (PTree.Node111 l1 x1 r) else if L.beq x x2 then CC (PTree.Node111 l1 x2 r) else CC (PTree.Node111 l1 x r)
  | Same2, None, Same => CC (PTree.Node101 l2 r2)
  | Same2, None, Same1 => CC (PTree.Node101 l2 r1)
  | Same2, None, Same2 => CC (PTree.Node101 l2 r2)
  | Same2, None, CC0 =>CC (PTree.Node100 l2)
  | Same2, None, CC r => CC (PTree.Node101 l2 r)
  | Same2, Some x, Same => if L.beq x x1 then CC (PTree.Node111 l2 x1 r2) else if L.beq x x2 then Same2 else CC (PTree.Node111 l2 x r2)
  | Same2, Some x, Same1 => if L.beq x x1 then CC (PTree.Node111 l2 x1 r1) else if L.beq x x2 then CC (PTree.Node111 l2 x2 r1) else CC (PTree.Node111 l2 x r1)
  | Same2, Some x, Same2 => if L.beq x x1 then CC (PTree.Node111 l2 x1 r2) else if L.beq x x2 then Same2 else CC (PTree.Node111 l2 x r2)
  | Same2, Some x, CC0 => if L.beq x x1 then CC (PTree.Node110 l2 x1) else if L.beq x x2 then CC (PTree.Node110 l2 x2) else CC (PTree.Node110 l2 x)
  | Same2, Some x, CC r => if L.beq x x1 then CC (PTree.Node111 l2 x1 r) else if L.beq x x2 then CC (PTree.Node111 l2 x2 r) else CC (PTree.Node111 l2 x r)
  | CC0, None, Same => CC (PTree.Node001 r2)
  | CC0, None, Same1 => CC (PTree.Node001 r1)
  | CC0, None, Same2 => CC (PTree.Node001 r2)
  | CC0, None, CC0 => CC0
  | CC0, None, CC r => CC (PTree.Node001 r)
  | CC0, Some x, Same => if L.beq x x1 then CC (PTree.Node011 x1 r2) else if L.beq x x2 then CC (PTree.Node011 x2 r2) else CC (PTree.Node011 x r2)
  | CC0, Some x, Same1 => if L.beq x x1 then CC (PTree.Node011 x1 r1) else if L.beq x x2 then CC (PTree.Node011 x2 r1) else CC (PTree.Node011 x r1)
  | CC0, Some x, Same2 => if L.beq x x1 then CC (PTree.Node011 x1 r2) else if L.beq x x2 then CC (PTree.Node011 x2 r2) else CC (PTree.Node011 x r2)
  | CC0, Some x, CC0 => if L.beq x x1 then CC (PTree.Node010 x1) else if L.beq x x2 then CC (PTree.Node010 x2) else CC (PTree.Node010 x)
  | CC0, Some x, CC r => if L.beq x x1 then CC (PTree.Node011 x1 r) else if L.beq x x2 then CC (PTree.Node011 x2 r) else CC (PTree.Node011 x r)
  | CC l, None, Same => CC (PTree.Node101 l r2)
  | CC l, None, Same1 => CC (PTree.Node101 l r1)
  | CC l, None, Same2 => CC (PTree.Node101 l r2)
  | CC l, None, CC0 => CC (PTree.Node100 l)
  | CC l, None, CC r => CC (PTree.Node101 l r)
  | CC l, Some x, Same => if L.beq x x1 then CC (PTree.Node111 l x1 r2) else if L.beq x x2 then CC (PTree.Node111 l x2 r2) else CC (PTree.Node111 l x r2)
  | CC l, Some x, Same1 => if L.beq x x1 then CC (PTree.Node111 l x1 r1) else if L.beq x x2 then CC (PTree.Node111 l x2 r1) else CC (PTree.Node111 l x r1)
  | CC l, Some x, Same2 => if L.beq x x1 then CC (PTree.Node111 l x1 r2) else if L.beq x x2 then CC (PTree.Node111 l x2 r2) else CC (PTree.Node111 l x r2)
  | CC l, Some x, CC0 => if L.beq x x1 then CC (PTree.Node110 l x1) else if L.beq x x2 then CC (PTree.Node110 l x2) else CC (PTree.Node110 l x)
  | CC l, Some x, CC r => if L.beq x x1 then CC (PTree.Node111 l x1 r) else if L.beq x x2 then CC (PTree.Node111 l x2 r) else CC (PTree.Node111 l x r)
  end
 end.

Lemma xcombine_l_combine': 
  forall m,
 PTree.xcombine_l f (PTree.Nodes m) = PTree.combine' f m PTree.Empty.
Proof.
intros.
rewrite PTree.combine'_Empty.
reflexivity.
Qed.

Lemma combine_commut_f     : forall m1 m2 : PTree.t L.t,
       PTree.combine f m1 m2 = PTree.combine (fun i j : option L.t => f j i) m2 m1.
Proof. intros. apply (PTree.combine_commut f  (fun i j => f j i) f_none_none); reflexivity.
Qed.


Lemma xcombine_r_combine': 
  forall m,
 PTree.xcombine_r f (PTree.Nodes m) = PTree.combine' (flip f) m PTree.Empty.
Proof. intros. 
fold (PTree.combine (flip f) (PTree.Nodes m) PTree.Empty).
rewrite <- combine_commut_f; auto.
Qed.

Lemma xcombine_eq:
  forall m1 m2,
  match xcombine m1 m2 with
  | Same => tree_eq (PTree.Nodes m1) (PTree.combine f (PTree.Nodes m1) (PTree.Nodes m2))
                 /\ tree_eq (PTree.Nodes m2) (PTree.combine f (PTree.Nodes m1) (PTree.Nodes m2))
  | Same1 => tree_eq (PTree.Nodes m1) (PTree.combine f (PTree.Nodes m1) (PTree.Nodes m2))
  | Same2 => tree_eq (PTree.Nodes m2) (PTree.combine f (PTree.Nodes m1) (PTree.Nodes m2))
  | CC0 => tree_eq PTree.Empty  (PTree.combine f (PTree.Nodes m1) (PTree.Nodes m2))
  | CC m => tree_eq (PTree.Nodes m) (PTree.combine f (PTree.Nodes m1) (PTree.Nodes m2))
  end.
Proof.
(*Opaque combine_l combine_r PTree.xcombine_l PTree.xcombine_r. *)
  induction m1 as [r1 IHr1 | x1 | x1 r1 IHr1 | l1 IHl1 | l1 IHl1 r1 IHr1 | l1 IHl1 x1 | l1 IHl1 x1 r1 IHr1 ];
  destruct m2 as [r2|x2|x2 r2|l2|l2 r2|l2 x2|l2 x2 r2];
  unfold xcombine; fold xcombine.
all: try solve [

repeat match goal with 
|  H: tree_eq _ _ /\ tree_eq _ _ |- _ => destruct H 
| |- context [xcombine ?a ?b] =>
  match goal with IH: forall m2, match xcombine a m2 with _ => _ end |- _ =>
     specialize (IH b); destruct (xcombine a b) eqn:?H
  end
| |- context [f ?a ?b] => destruct (f a b) eqn:Hf
| |- context [combine_l ?a] =>
  match goal with
  | IH: forall m2, match xcombine a m2 with _ => _ end |- _ =>
     clear IH; destruct (combine_l a) eqn:IH; apply combine_l_eq in IH
  | |- _ =>  let H := fresh in destruct (combine_l a) eqn:?H; apply combine_l_eq in H
  end
| |- context [combine_r ?a] =>
  match goal with
  | IH: forall m2, match xcombine a m2 with _ => _ end |- _ =>
     clear IH; destruct (combine_r a) eqn:IH; apply combine_r_eq in IH
  | |- _ =>  let H := fresh in destruct (combine_r a) eqn:?H; apply combine_r_eq in H
  end

| |- context [L.beq ?a ?b] => 
  let H := fresh in 
   destruct (L.beq a b) eqn:H; [apply L.beq_correct in H | clear H]
| |- tree_eq _ _ /\ tree_eq _ _ => split
end;
 try solve [
intro i; destruct i;
 repeat match goal with H: tree_eq _ _ |- _ => specialize (H i) end;
 unfold PTree.get in *;
 unfold PTree.get'; fold @PTree.get';
 try match goal with |- opt_eq (PTree.get' ?i ?a) _ => 
   match goal with H: opt_eq (PTree.get' i a) _ |- _ => eapply opt_eq_trans; [apply H | clear H] end
 end;

 unfold PTree.combine in *;
 simpl PTree.combine'; unfold PTree.Node;
 rewrite ?Hf, ?f_none_none;
 repeat change (PTree.xcombine' _ ?r) with (PTree.xcombine_r f (PTree.Nodes r));
 rewrite ?xcombine_l_combine', ?xcombine_r_combine' in *;
 repeat match goal with |- context [PTree.combine' ?g ?a ?b] =>
  destruct (PTree.combine' g a b) eqn:?H
 end;
 try apply opt_eq_refl;
 auto; 
 try apply L.eq_refl;
 try (apply L.eq_sym; auto);
 try match goal with 
  | H: tree_eq (PTree.Nodes _) PTree.Empty |- _ => contradiction (tree_eq_Nodes_not_Empty H) 
  end
]
].
Qed.

Definition combine (m1 m2: PTree.t L.t) : PTree.t L.t :=
  match m1, m2 with
  | PTree.Empty, PTree.Empty => PTree.Empty
  | PTree.Empty, PTree.Nodes m2' => 
       match combine_r m2' with
       | Unchanged => m2 
       | Chempty => PTree.Empty 
       | Changed m => PTree.Nodes m
      end
  | PTree.Nodes m1', PTree.Empty => 
       match combine_l m1' with
       | Unchanged => m1 
       | Chempty => PTree.Empty 
       | Changed m => PTree.Nodes m
      end
  | PTree.Nodes m1', PTree.Nodes m2' =>
    match xcombine m1' m2' with
     | Same|Same1 => m1
     | Same2 => m2
     | CC0 => PTree.Empty
     | CC m => PTree.Nodes m
     end
  end.

Lemma gcombine:
  forall m1 m2 i, opt_eq (PTree.get i (combine m1 m2)) (f (PTree.get i m1) (PTree.get i m2)).
Proof.
  intros.
  assert (tree_eq (combine m1 m2) (PTree.combine f m1 m2)). {
    unfold combine.
    destruct m1, m2.
    apply tree_eq_refl.
    destruct (combine_r t0) eqn:H; apply combine_r_eq in H; apply H.
    destruct (combine_l t0) eqn:H; apply combine_l_eq in H.
    rewrite xcombine_l_combine' in H. apply H.
    rewrite xcombine_l_combine' in H. apply H.
    rewrite xcombine_l_combine' in H. apply H.
    pose proof (xcombine_eq t0 t1).
    destruct (xcombine t0 t1); apply H.
  }
  eapply opt_eq_trans. apply H. rewrite PTree.gcombine; auto. apply opt_eq_refl.
Qed.

End COMBINE.

Definition lub (x y: t) : t :=
  combine
    (fun a b =>
       match a, b with
       | Some u, Some v => Some (L.lub u v)
       | None, _ => b
       | _, None => a
       end)
    x y.

Lemma gcombine_bot:
  forall f t1 t2 p,
  f None None = None ->
  L.eq (get p (combine f t1 t2))
       (match f t1!p t2!p with Some x => x | None => L.bot end).
Proof.
  intros. unfold get. generalize (gcombine f H t1 t2 p). unfold opt_eq.
  destruct ((combine f t1 t2)!p); destruct (f t1!p t2!p).
  auto. contradiction. contradiction. intros; apply L.eq_refl.
Qed.

Lemma ge_lub_left:
  forall x y, ge (lub x y) x.
Proof.
  unfold ge, lub; intros.
  eapply L.ge_trans. apply L.ge_refl. apply gcombine_bot; auto.
  unfold get. destruct x!p. destruct y!p.
  apply L.ge_lub_left.
  apply L.ge_refl. apply L.eq_refl.
  apply L.ge_bot.
Qed.

Lemma ge_lub_right:
  forall x y, ge (lub x y) y.
Proof.
  unfold ge, lub; intros.
  eapply L.ge_trans. apply L.ge_refl. apply gcombine_bot; auto.
  unfold get. destruct y!p. destruct x!p.
  apply L.ge_lub_right.
  apply L.ge_refl. apply L.eq_refl.
  apply L.ge_bot.
Qed.

End LPMap1.

(** Given a semi-lattice with top [L], the following functor implements
  a semi-lattice-with-top structure over finite maps from positive numbers to [L.t].
  The default value for these maps is [L.top].  Bottom elements are smashed. *)

Module LPMap(L: SEMILATTICE_WITH_TOP) <: SEMILATTICE_WITH_TOP.

Inductive t' : Type :=
  | Bot: t'
  | Top_except: PTree.t L.t -> t'.

Definition t: Type := t'.

Definition get (p: positive) (x: t) : L.t :=
  match x with
  | Bot => L.bot
  | Top_except m => match m!p with None => L.top | Some x => x end
  end.

Definition set (p: positive) (v: L.t) (x: t) : t :=
  match x with
  | Bot => Bot
  | Top_except m =>
      if L.beq v L.bot
      then Bot
      else Top_except (if L.beq v L.top then PTree.remove p m else PTree.set p v m)
  end.

Lemma gsspec:
  forall p v x q,
  x <> Bot -> ~L.eq v L.bot ->
  L.eq (get q (set p v x)) (if peq q p then v else get q x).
Proof.
  intros. unfold set. destruct x. congruence.
  destruct (L.beq v L.bot) eqn:EBOT.
  elim H0. apply L.beq_correct; auto.
  destruct (L.beq v L.top) eqn:ETOP; simpl.
  rewrite PTree.grspec. unfold PTree.elt_eq. destruct (peq q p).
  apply L.eq_sym. apply L.beq_correct; auto.
  apply L.eq_refl.
  rewrite PTree.gsspec. destruct (peq q p); apply L.eq_refl.
Qed.

Definition eq (x y: t) : Prop :=
  forall p, L.eq (get p x) (get p y).

Lemma eq_refl: forall x, eq x x.
Proof.
  unfold eq; intros. apply L.eq_refl.
Qed.

Lemma eq_sym: forall x y, eq x y -> eq y x.
Proof.
  unfold eq; intros. apply L.eq_sym; auto.
Qed.

Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
Proof.
  unfold eq; intros. eapply L.eq_trans; eauto.
Qed.

Definition beq (x y: t) : bool :=
  match x, y with
  | Bot, Bot => true
  | Top_except m, Top_except n => PTree.beq L.beq m n
  | _, _ => false
  end.

Lemma beq_correct: forall x y, beq x y = true -> eq x y.
Proof.
  destruct x; destruct y; simpl; intro; try congruence.
  apply eq_refl.
  red; intro; simpl.
  rewrite PTree.beq_correct in H. generalize (H p).
  destruct (t0!p); destruct (t1!p); intuition.
  apply L.beq_correct; auto.
  apply L.eq_refl.
Qed.

Definition ge (x y: t) : Prop :=
  forall p, L.ge (get p x) (get p y).

Lemma ge_refl: forall x y, eq x y -> ge x y.
Proof.
  unfold ge, eq; intros. apply L.ge_refl. auto.
Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof.
  unfold ge; intros. apply L.ge_trans with (get p y); auto.
Qed.

Definition bot := Bot.

Lemma get_bot: forall p, get p bot = L.bot.
Proof.
  unfold bot; intros; simpl. auto.
Qed.

Lemma ge_bot: forall x, ge x bot.
Proof.
  unfold ge; intros. rewrite get_bot. apply L.ge_bot.
Qed.

Definition top := Top_except (PTree.empty L.t).

Lemma get_top: forall p, get p top = L.top.
Proof.
  unfold top; intros; simpl. auto.
Qed.

Lemma ge_top: forall x, ge top x.
Proof.
  unfold ge; intros. rewrite get_top. apply L.ge_top.
Qed.

Module LM := LPMap1(L).

Definition opt_lub (x y: L.t) : option L.t :=
  let z := L.lub x y in
  if L.beq z L.top then None else Some z.

Definition lub (x y: t) : t :=
  match x, y with
  | Bot, _ => y
  | _, Bot => x
  | Top_except m, Top_except n =>
      Top_except
        (LM.combine
           (fun a b =>
              match a, b with
              | Some u, Some v => opt_lub u v
              | _, _ => None
              end)
           m n)
  end.

Lemma gcombine_top:
  forall f t1 t2 p,
  f None None = None ->
  L.eq (get p (Top_except (LM.combine f t1 t2)))
       (match f t1!p t2!p with Some x => x | None => L.top end).
Proof.
  intros. simpl. generalize (LM.gcombine f H t1 t2 p). unfold LM.opt_eq.
  destruct ((LM.combine f t1 t2)!p); destruct (f t1!p t2!p).
  auto. contradiction. contradiction. intros; apply L.eq_refl.
Qed.

Lemma ge_lub_left:
  forall x y, ge (lub x y) x.
Proof.
  unfold ge, lub; intros. destruct x; destruct y.
  rewrite get_bot. apply L.ge_bot.
  rewrite get_bot. apply L.ge_bot.
  apply L.ge_refl. apply L.eq_refl.
  eapply L.ge_trans. apply L.ge_refl. apply gcombine_top; auto.
  unfold get. destruct t0!p. destruct t1!p.
  unfold opt_lub. destruct (L.beq (L.lub t2 t3) L.top) eqn:E.
  apply L.ge_top. apply L.ge_lub_left.
  apply L.ge_top.
  apply L.ge_top.
Qed.

Lemma ge_lub_right:
  forall x y, ge (lub x y) y.
Proof.
  unfold ge, lub; intros. destruct x; destruct y.
  rewrite get_bot. apply L.ge_bot.
  apply L.ge_refl. apply L.eq_refl.
  rewrite get_bot. apply L.ge_bot.
  eapply L.ge_trans. apply L.ge_refl. apply gcombine_top; auto.
  unfold get. destruct t0!p; destruct t1!p.
  unfold opt_lub. destruct (L.beq (L.lub t2 t3) L.top) eqn:E.
  apply L.ge_top. apply L.ge_lub_right.
  apply L.ge_top.
  apply L.ge_top.
  apply L.ge_top.
Qed.

End LPMap.

(** * Semi-lattice over a set. *)

(** Given a set [S: FSetInterface.S], the following functor
    implements a semi-lattice over these sets, ordered by inclusion. *)

Module LFSet (S: FSetInterface.WS) <: SEMILATTICE.

  Definition t := S.t.

  Definition eq (x y: t) := S.Equal x y.
  Definition eq_refl: forall x, eq x x := S.eq_refl.
  Definition eq_sym: forall x y, eq x y -> eq y x := S.eq_sym.
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := S.eq_trans.
  Definition beq: t -> t -> bool := S.equal.
  Definition beq_correct: forall x y, beq x y = true -> eq x y := S.equal_2.

  Definition ge (x y: t) := S.Subset y x.
  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    unfold eq, ge, S.Equal, S.Subset; intros. firstorder.
  Qed.
  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    unfold ge, S.Subset; intros. eauto.
  Qed.

  Definition  bot: t := S.empty.
  Lemma ge_bot: forall x, ge x bot.
  Proof.
    unfold ge, bot, S.Subset; intros. elim (S.empty_1 H).
  Qed.

  Definition lub: t -> t -> t := S.union.

  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    unfold lub, ge, S.Subset; intros. apply S.union_2; auto.
  Qed.

  Lemma ge_lub_right: forall x y, ge (lub x y) y.
  Proof.
    unfold lub, ge, S.Subset; intros. apply S.union_3; auto.
  Qed.

End LFSet.

(** * Flat semi-lattice *)

(** Given a type with decidable equality [X], the following functor
  returns a semi-lattice structure over [X.t] complemented with
  a top and a bottom element.  The ordering is the flat ordering
  [Bot < Inj x < Top]. *)

Module LFlat(X: EQUALITY_TYPE) <: SEMILATTICE_WITH_TOP.

Inductive t' : Type :=
  | Bot: t'
  | Inj: X.t -> t'
  | Top: t'.

Definition t : Type := t'.

Definition eq (x y: t) := (x = y).
Definition eq_refl: forall x, eq x x := (@eq_refl t).
Definition eq_sym: forall x y, eq x y -> eq y x := (@eq_sym t).
Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@eq_trans t).

Definition beq (x y: t) : bool :=
  match x, y with
  | Bot, Bot => true
  | Inj u, Inj v => if X.eq u v then true else false
  | Top, Top => true
  | _, _ => false
  end.

Lemma beq_correct: forall x y, beq x y = true -> eq x y.
Proof.
  unfold eq; destruct x; destruct y; simpl; try congruence; intro.
  destruct (X.eq t0 t1); congruence.
Qed.

Definition ge (x y: t) : Prop :=
  match x, y with
  | Top, _ => True
  | _, Bot => True
  | Inj a, Inj b => a = b
  | _, _ => False
  end.

Lemma ge_refl: forall x y, eq x y -> ge x y.
Proof.
  unfold eq, ge; intros; subst y; destruct x; auto.
Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof.
  unfold ge; destruct x; destruct y; try destruct z; intuition.
  transitivity t1; auto.
Qed.

Definition bot: t := Bot.

Lemma ge_bot: forall x, ge x bot.
Proof.
  destruct x; simpl; auto.
Qed.

Definition top: t := Top.

Lemma ge_top: forall x, ge top x.
Proof.
  destruct x; simpl; auto.
Qed.

Definition lub (x y: t) : t :=
  match x, y with
  | Bot, _ => y
  | _, Bot => x
  | Top, _ => Top
  | _, Top => Top
  | Inj a, Inj b => if X.eq a b then Inj a else Top
  end.

Lemma ge_lub_left: forall x y, ge (lub x y) x.
Proof.
  destruct x; destruct y; simpl; auto.
  case (X.eq t0 t1); simpl; auto.
Qed.

Lemma ge_lub_right: forall x y, ge (lub x y) y.
Proof.
  destruct x; destruct y; simpl; auto.
  case (X.eq t0 t1); simpl; auto.
Qed.

End LFlat.

(** * Boolean semi-lattice *)

(** This semi-lattice has only two elements, [bot] and [top], trivially
  ordered. *)

Module LBoolean <: SEMILATTICE_WITH_TOP.

Definition t := bool.

Definition eq (x y: t) := (x = y).
Definition eq_refl: forall x, eq x x := (@eq_refl t).
Definition eq_sym: forall x y, eq x y -> eq y x := (@eq_sym t).
Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@eq_trans t).

Definition beq : t -> t -> bool := eqb.

Lemma beq_correct: forall x y, beq x y = true -> eq x y.
Proof eqb_prop.

Definition ge (x y: t) : Prop := x = y \/ x = true.

Lemma ge_refl: forall x y, eq x y -> ge x y.
Proof. unfold ge; tauto. Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof. unfold ge; intuition congruence. Qed.

Definition bot := false.

Lemma ge_bot: forall x, ge x bot.
Proof. destruct x; compute; tauto. Qed.

Definition top := true.

Lemma ge_top: forall x, ge top x.
Proof. unfold ge, top; tauto. Qed.

Definition lub (x y: t) := x || y.

Lemma ge_lub_left: forall x y, ge (lub x y) x.
Proof. destruct x; destruct y; compute; tauto. Qed.

Lemma ge_lub_right: forall x y, ge (lub x y) y.
Proof. destruct x; destruct y; compute; tauto. Qed.

End LBoolean.

(** * Option semi-lattice *)

(** This lattice adds a top element (represented by [None]) to a given
  semi-lattice (whose elements are injected via [Some]). *)

Module LOption(L: SEMILATTICE) <: SEMILATTICE_WITH_TOP.

Definition t: Type := option L.t.

Definition eq (x y: t) : Prop :=
  match x, y with
  | None, None => True
  | Some x1, Some y1 => L.eq x1 y1
  | _, _ => False
  end.

Lemma eq_refl: forall x, eq x x.
Proof.
  unfold eq; intros; destruct x. apply L.eq_refl. auto.
Qed.

Lemma eq_sym: forall x y, eq x y -> eq y x.
Proof.
  unfold eq; intros; destruct x; destruct y; auto. apply L.eq_sym; auto.
Qed.

Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
Proof.
  unfold eq; intros; destruct x; destruct y; destruct z; auto.
  eapply L.eq_trans; eauto.
  contradiction.
Qed.

Definition beq (x y: t) : bool :=
  match x, y with
  | None, None => true
  | Some x1, Some y1 => L.beq x1 y1
  | _, _ => false
  end.

Lemma beq_correct: forall x y, beq x y = true -> eq x y.
Proof.
  unfold beq, eq; intros; destruct x; destruct y.
  apply L.beq_correct; auto.
  discriminate. discriminate. auto.
Qed.

Definition ge (x y: t) : Prop :=
  match x, y with
  | None, _ => True
  | _, None => False
  | Some x1, Some y1 => L.ge x1 y1
  end.

Lemma ge_refl: forall x y, eq x y -> ge x y.
Proof.
  unfold eq, ge; intros; destruct x; destruct y.
  apply L.ge_refl; auto.
  auto. elim H. auto.
Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof.
  unfold ge; intros; destruct x; destruct y; destruct z; auto.
  eapply L.ge_trans; eauto. contradiction.
Qed.

Definition bot : t := Some L.bot.

Lemma ge_bot: forall x, ge x bot.
Proof.
  unfold ge, bot; intros. destruct x; auto. apply L.ge_bot.
Qed.

Definition lub (x y: t) : t :=
  match x, y with
  | None, _ => None
  | _, None => None
  | Some x1, Some y1 => Some (L.lub x1 y1)
  end.

Lemma ge_lub_left: forall x y, ge (lub x y) x.
Proof.
  unfold ge, lub; intros; destruct x; destruct y; auto. apply L.ge_lub_left.
Qed.

Lemma ge_lub_right: forall x y, ge (lub x y) y.
Proof.
  unfold ge, lub; intros; destruct x; destruct y; auto. apply L.ge_lub_right.
Qed.

Definition top : t := None.

Lemma ge_top: forall x, ge top x.
Proof.
  unfold ge, top; intros. auto.
Qed.

End LOption.
