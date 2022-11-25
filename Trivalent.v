(* Boolean t. *)
Inductive T :=
| true : T
| false : T.
Notation "⊤" := true.
Notation "⊥" := false.

Definition T_elim {a : Type} (p : T) (v1 v2 : a) : a :=
  match p with
  | ⊤ => v1
  | ⊥ => v2
  end.

(* Convenient to have. *)
Theorem T_not_eq : ~ (true = false).
Proof.
  intro.
  pose (eq_refl (T_elim true unit False)).
  replace (T_elim true unit False = T_elim true unit False) with
    (T_elim true unit False = T_elim false unit False)
    in e by now (rewrite H). 
  pose tt.
  unfold T_elim in e.
  rewrite e in u.
  exact u.
Qed.

(* Trivalent t#. *)
Inductive THash :=
| trueHash : THash
| falseHash : THash
| hash : THash.
Notation "T#" := THash.
Notation "⊤#" := trueHash.
Notation "⊥#" := falseHash.
Notation "#" := hash.

Definition THash_elim {a : Type} (p : T#) (v1 v2 v3 : a) : a :=
  match p with
  | ⊤# => v1
  | ⊥# => v2
  | # => v3
  end.

(* Convienent to have. *)
Theorem THash_not_eq : ~ (⊤# = ⊥#) /\ ~ (# = ⊤#) /\ ~ (# = ⊥#).
Proof.
  split.
  intro.
  pose (eq_refl (THash_elim ⊤# unit False unit)).
  replace (THash_elim ⊤# unit False unit =
             THash_elim ⊤# unit False unit) with
    (THash_elim ⊤# unit False unit =
       THash_elim ⊥# unit False unit)
    in e by now (rewrite H).
  pose tt.
  unfold THash_elim in e.
  rewrite e in u.
  exact u.
  split.
  intro.
  pose (eq_refl (THash_elim ⊤# unit unit False)).
  replace (THash_elim ⊤# unit unit False =
             THash_elim ⊤# unit unit False) with
    (THash_elim ⊤# unit unit False =
       THash_elim # unit unit False)
    in e by now (rewrite H).
  pose tt.
  unfold THash_elim in e.
  rewrite e in u.
  exact u.
  intro.
  pose (eq_refl (THash_elim ⊥# unit unit False)).
  replace (THash_elim ⊥# unit unit False =
             THash_elim ⊥# unit unit False) with
    (THash_elim ⊥# unit unit False =
       THash_elim # unit unit False)
    in e by now (rewrite H).
  pose tt.
  unfold THash_elim in e.
  rewrite e in u.
  exact u.
Qed.

(* The ``charitable'' trivalent existential quantifier, ∃#. *)
Parameter existsHash : forall {a : Set}, (a -> T#) -> T#.
Notation "∃# P" := (existsHash P) (at level 200).
Axiom existsHashDef1 :
  forall {a : Set} {k : a -> T#}, (exists (x : a), k x = ⊤#) -> (∃# k) = ⊤#.
Axiom existsHashDef1' :
  forall {a : Set} {k : a -> T#}, (∃# k) = ⊤# -> (exists (x : a), k x = ⊤#).
Axiom existsHashDef2 :
  forall {a : Set} {k : a -> T#},
    (exists (x : a), k x = ⊥#) /\ ~ (exists (x : a), k x = ⊤#) -> (∃# k) = ⊥#.
Axiom existsHashDef2' :
  forall {a : Set} {k : a -> T#},
    (∃# k) = ⊥# -> (exists (x : a), k x = ⊥#) /\ ~ (exists (x : a), k x = ⊤#).
Axiom existsHashDef3 :
  forall {a : Set} {k : a -> T#}, (forall (x : a), k x = #) -> (∃# k) = #.
Axiom existsHashDef3' :
  forall {a : Set} {k : a -> T#}, (∃# k) = # -> (forall (x : a), k x = #).

(* Weak Kleene ∧#. *)
Parameter andHash : T# -> T# -> T#.
Notation "A ∧# B" := (andHash A B) (at level 60, right associativity).
Axiom andHashDef1 : forall (x : T#), (x ∧# # = #) /\ (# ∧# x = #).
Axiom andHashDef2 : (⊤# ∧# ⊥# = ⊥#) /\ (⊥# ∧# ⊤# = ⊥#) /\ (⊥# ∧# ⊥# = ⊥#).
Axiom andHashDef3 : ⊤# ∧# ⊤# = ⊤#.

Lemma andHash_comm : forall (x y : T#), x ∧# y = y ∧# x.
Proof.
  intros.
  case_eq x.
  case_eq y.
  intros.
  trivial.
  intros.
  rewrite (proj1 andHashDef2).
  rewrite (proj1 (proj2 andHashDef2)).
  trivial.
  intros.
  rewrite (proj1 (andHashDef1 ⊤#)).
  rewrite (proj2 (andHashDef1 ⊤#)).
  trivial.
  intro.
  case_eq y.
  intro.
  rewrite (proj1 andHashDef2).
  rewrite (proj1 (proj2 andHashDef2)).
  trivial.
  intro.
  trivial.
  intro.
  rewrite (proj1 (andHashDef1 ⊥#)).
  rewrite (proj2 (andHashDef1 ⊥#)).
  trivial.
  intro.
  case_eq y.
  intro.
  rewrite (proj1 (andHashDef1 ⊤#)).
  rewrite (proj2 (andHashDef1 ⊤#)).
  trivial.
  intro.
  rewrite (proj1 (andHashDef1 ⊥#)).
  rewrite (proj2 (andHashDef1 ⊥#)).
  trivial.
  intro.
  trivial.
Qed.
  
Lemma andHash_assoc : forall (x y z : T#), x ∧# (y ∧# z) = (x ∧# y) ∧# z.
Proof.
  intros.
  case_eq x. case_eq y. case_eq z.
  intros.
  repeat rewrite andHashDef3. trivial.
  intros.
  rewrite andHashDef3.
  repeat rewrite (proj1 andHashDef2). trivial.
  intros.
  rewrite andHashDef3.
  repeat rewrite (proj1 (andHashDef1 ⊤#)). trivial.
  intros.
  case_eq z.
  intros.
  rewrite (proj1 andHashDef2).
  rewrite (proj1 (proj2 andHashDef2)).
  rewrite (proj1 andHashDef2). trivial.
  intros.
  rewrite (proj2 (proj2 andHashDef2)).
  rewrite (proj1 andHashDef2).
  rewrite (proj2 (proj2 andHashDef2)). trivial.
  intro.
  rewrite (proj1 andHashDef2).
  repeat rewrite (proj1 (andHashDef1 ⊥#)).
  rewrite (proj1 (andHashDef1 ⊤#)). trivial.
  intros.
  case_eq z.
  intros.
  rewrite (proj1 (andHashDef1 ⊤#)).
  repeat rewrite (proj2 (andHashDef1 ⊤#)).
  rewrite (proj1 (andHashDef1 ⊤#)). trivial.
  intro.
  rewrite (proj2 (andHashDef1 ⊥#)).
  rewrite (proj1 (andHashDef1 ⊤#)).
  rewrite (proj2 (andHashDef1 ⊥#)). trivial.
  intro.
  rewrite (proj2 (andHashDef1 #)).
  rewrite (proj1 (andHashDef1 ⊤#)).
  rewrite (proj2 (andHashDef1 #)). trivial.
  case_eq y.
  case_eq z.
  intros.
  rewrite andHashDef3.
  repeat rewrite (proj1 (proj2 andHashDef2)). trivial.
  intros.
  rewrite (proj1 (proj2 andHashDef2)).
  rewrite (proj1 andHashDef2).
  repeat rewrite (proj2 (proj2 andHashDef2)). trivial.
  intros.
  rewrite (proj1 (andHashDef1 ⊤#)).
  rewrite (proj1 (proj2 andHashDef2)).
  repeat rewrite (proj1 (andHashDef1 ⊥#)). trivial.
  intros.
  case_eq z.
  intros.
  rewrite (proj1 (proj2 andHashDef2)).
  repeat rewrite (proj2 (proj2 andHashDef2)).
  rewrite (proj1 (proj2 andHashDef2)). trivial.
  intro.
  repeat rewrite (proj2 (proj2 andHashDef2)). trivial.
  intro.
  rewrite (proj2 (proj2 andHashDef2)).
  repeat rewrite (proj1 (andHashDef1 ⊥#)). trivial.
  intros.
  case_eq z.
  intro.
  rewrite (proj1 (andHashDef1 ⊥#)).
  repeat rewrite (proj2 (andHashDef1 ⊤#)).
  rewrite (proj1 (andHashDef1 ⊥#)). trivial.
  intro.
  rewrite (proj1 (andHashDef1 ⊥#)).
  rewrite (proj2 (andHashDef1 ⊥#)).
  rewrite (proj1 (andHashDef1 ⊥#)). trivial.
  intro.
  rewrite (proj1 (andHashDef1 #)).
  repeat rewrite (proj1 (andHashDef1 ⊥#)).
  rewrite (proj1 (andHashDef1 #)). trivial.
  case_eq y.
  case_eq z.
  intros.
  rewrite andHashDef3.
  repeat rewrite (proj2 (andHashDef1 ⊤#)). trivial.
  intros.
  rewrite (proj1 andHashDef2).
  rewrite (proj2 (andHashDef1 ⊤#)). trivial.
  intros.
  rewrite (proj2 (andHashDef1 ⊤#)).
  rewrite (proj1 (andHashDef1 ⊤#)). trivial.
  case_eq z.
  intros.
  rewrite (proj2 (andHashDef1 ⊥#)).
  rewrite (proj1 (proj2 andHashDef2)).
  rewrite (proj2 (andHashDef1 ⊥#)).
  rewrite (proj2 (andHashDef1 ⊤#)). trivial.
  intros.
  rewrite (proj2 (proj2 andHashDef2)).
  repeat rewrite (proj2 (andHashDef1 ⊥#)). trivial.
  intros.
  rewrite (proj2 (andHashDef1 ⊥#)).
  rewrite (proj1 (andHashDef1 ⊥#)). trivial.
  case_eq z.
  intros.
  rewrite (proj2 (andHashDef1 ⊤#)).
  repeat rewrite (proj2 (andHashDef1 #)).
  rewrite (proj2 (andHashDef1 ⊤#)). trivial.
  intros.
  rewrite (proj2 (andHashDef1 ⊥#)).
  repeat rewrite (proj2 (andHashDef1 #)).
  rewrite (proj2 (andHashDef1 ⊥#)). trivial.
  intros.
  repeat rewrite (proj2 (andHashDef1 #)). trivial.
Qed.
 
Lemma andHash_is_true : forall {x  y : T#}, x ∧# y = ⊤# -> (x = ⊤# /\ y = ⊤#).
Proof.
  intros.
  case_eq x.
  case_eq y.
  intros.
  auto.
  intros.
  rewrite H0 in H.
  rewrite H1 in H.
  rewrite (proj1 andHashDef2) in H.
  exact (conj eq_refl H).
  intros.
  rewrite H0 in H.
  rewrite H1 in H.
  rewrite (proj1 (andHashDef1 ⊤#)) in H.
  exact (conj eq_refl H).
  intros.
  rewrite H0 in H.
  case_eq y.
  intros.
  rewrite H1 in H.
  rewrite (proj1 (proj2 andHashDef2)) in H.
  exact (conj H eq_refl).
  intros.
  rewrite H1 in H.
  rewrite (proj2 (proj2 andHashDef2)) in H.
  exact (conj H H).
  intros.
  rewrite H1 in H.
  rewrite (proj1 (andHashDef1 ⊥#)) in H.
  pose (proj1 (proj2 THash_not_eq) H).
  inversion f.
  intros.
  rewrite H0 in H.
  case_eq y.
  intros.
  rewrite H1 in H.
  rewrite (proj2 (andHashDef1 ⊤#)) in H.
  pose (proj1 (proj2 THash_not_eq) H).
  inversion f.
  intros.
  rewrite H1 in H.
  rewrite (proj2 (andHashDef1 ⊥#)) in H.
  pose (proj1 (proj2 THash_not_eq) H).
  inversion f.
  intros.
  rewrite H1 in H.
  rewrite (proj1 (andHashDef1 #)) in H.
  exact (conj H H).
Qed.

Lemma andHash_is_false1 : forall {x y : T#}, x ∧# y = ⊥# -> (x = ⊥# \/ y = ⊥#).
Proof.
  intros.
  case_eq x.
  intro.
  case_eq y.
  intro.
  rewrite H0 in H.
  rewrite H1 in H.
  rewrite andHashDef3 in H.
  pose (proj1 THash_not_eq H).
  inversion f.
  intro.
  right. trivial.
  intro.
  rewrite H0 in H.
  rewrite H1 in H.
  rewrite (proj1 (andHashDef1 ⊤#)) in H.
  pose (proj2 (proj2 THash_not_eq) H).
  inversion f.
  intro.
  left. trivial.
  intro.
  case_eq y.
  intro.
  rewrite H0 in H.
  rewrite H1 in H.
  rewrite (proj2 (andHashDef1 ⊤#)) in H.
  pose (proj2 (proj2 THash_not_eq) H).
  inversion f.
  intro.
  right. trivial.
  intro.
  rewrite H0 in H.
  rewrite H1 in H.
  rewrite (proj1 (andHashDef1 #)) in H.
  pose (proj2 (proj2 THash_not_eq) H).
  inversion f.
Qed.

Lemma andHash_is_false2 :
  forall {x y : T#}, x ∧# y = ⊥# -> (x = ⊤# \/ x = ⊥#) /\ (y = ⊤# \/ y = ⊥#).
Proof.
  assert (forall (x y : T#), x ∧# y = ⊥# -> (x = ⊤# \/ x = ⊥#)). intros.
  case_eq x. intro.
  left. trivial.
  intro.
  right. trivial.
  intro.
  rewrite H0 in H.
  rewrite (proj2 (andHashDef1 y)) in H.
  pose (proj2 (proj2 THash_not_eq) H).
  inversion f.
  intros.
  split.
  exact (H x y H0).
  rewrite (andHash_comm x y) in H0.
  exact (H y x H0).
Qed.
 
Lemma andHash_is_hash : forall {x y : T#}, x ∧# y = # -> (x = # \/ y = #).
Proof.
  intros.
  case_eq x.
  intro.
  case_eq y.
  intro.
  rewrite H0 in H.
  rewrite H1 in H.
  rewrite andHashDef3 in H.
  pose (proj1 (proj2 THash_not_eq) (eq_sym H)).
  inversion f.
  intro.
  rewrite H0 in H.
  rewrite H1 in H.
  rewrite (proj1 andHashDef2) in H.
  pose (proj2 (proj2 THash_not_eq) (eq_sym H)).
  inversion f.
  intro.
  right.
  trivial.
  intro.
  case_eq y.
  intro.
  rewrite H0 in H.
  rewrite H1 in H.
  rewrite (proj1 (proj2 andHashDef2)) in H.
  pose (proj2 (proj2 THash_not_eq) (eq_sym H)).
  inversion f.
  intro.
  rewrite H0 in H.
  rewrite H1 in H.
  rewrite (proj2 (proj2 andHashDef2)) in H.
  left.
  trivial.
  intro.
  right.
  trivial.
  intro.
  left.
  trivial.
Qed.

Lemma andHash_existsHash_comm :
  forall {a : Set} (φ : a -> T#) (p : T#),
    (∃# φ) ∧# p = ∃# (fun x : a => φ x ∧# p).
Proof.
  intros.
  case_eq ((∃# φ) ∧# p).
  intro.
  pose (andHash_is_true H).
  pose (existsHashDef1' (proj1 a0)).
  elim e.
  intros.
  pose andHashDef3.
  replace (⊤# ∧# ⊤# = ⊤#) with
    (φ x ∧# ⊤# = ⊤#) in e0 by now (rewrite (eq_sym H0)).
  replace (φ x ∧# ⊤# = ⊤#) with
    (φ x ∧# p = ⊤#) in e0 by now (rewrite (proj2 a0)).
  exact (eq_sym
           (existsHashDef1
              (ex_intro (fun x0 : a => (φ x0) ∧# p = ⊤#) x e0))).
  intro.
  pose (andHash_is_false1 H).
  elim o.
  intro.
  pose (existsHashDef2' H0).
  assert (exists x : a, (φ x) ∧# p = ⊥#).
  elim (proj1 a0).
  intros.
  case_eq p.
  intro.
  pose (proj1 (proj2 andHashDef2)).
  replace (andHash ⊥# ⊤# = ⊥#) with
    (φ x ∧# ⊤# = ⊥#) in e by now (rewrite (eq_sym H1)).
  exact (ex_intro (fun x0 : a => (φ x0) ∧# ⊤# = ⊥#) x e).
  intro.
  pose (proj2 (proj2 andHashDef2)).
  replace (⊥# ∧# ⊥# = ⊥#) with
    (φ x ∧# ⊥# = ⊥#) in e by now (rewrite (eq_sym H1)).
  exact (ex_intro (fun x0 : a => φ x0 ∧# ⊥# = ⊥#) x e).
  intro.
  pose H.
  rewrite H2 in e.
  rewrite (proj1 (andHashDef1 (existsHash φ))) in e.
  pose (proj2 (proj2 THash_not_eq) e).
  inversion f.
  assert (~ (exists x : a, φ x ∧# p = ⊤#)).
  intro.
  elim H2.
  intros.
  exact (proj2 a0 (ex_intro
                     (fun x => φ x = ⊤#)
                     x (proj1 (andHash_is_true H3)))).
  exact (eq_sym (existsHashDef2 (conj H1 H2))).
  intro.
  rewrite H0.
  case_eq (existsHash φ). intro.
  pose (existsHashDef1' H1).
  elim e. intros.
  pose (proj1 andHashDef2).
  rewrite (eq_sym H2) in e0.
  pose (ex_intro (fun x : a => φ x ∧# ⊥# = ⊥#) x e0).
  assert (~ exists x : a, φ x ∧# ⊥# = ⊤#). intro.
  elim H3. intros.
  exact (proj1 THash_not_eq
           (eq_sym (proj2 (andHash_is_true H4)))).
  exact (eq_sym (existsHashDef2 (conj e1 H3))).
  intro.
  pose (existsHashDef2' H1).
  assert (exists x : a, (φ x) ∧# ⊥# = ⊥#).
  elim (proj1 a0). intros.
  pose (proj2 (proj2 andHashDef2)).
  replace (⊥# ∧# ⊥# = ⊥#) with
    (φ x ∧# ⊥# = ⊥#) in e by now (rewrite (eq_sym H2)).
  exact (ex_intro (fun x0 : a => φ x0 ∧# ⊥# = ⊥#) x e).
  assert (~ exists x : a, φ x ∧# ⊥# = ⊤#). intro.
  elim H3. intros.
  exact (proj1 THash_not_eq
           (eq_sym (proj2 (andHash_is_true H4)))).
  exact (eq_sym (existsHashDef2 (conj H2 H3))).
  intro.
  elim (proj1 (andHash_is_false2 H)). intro.
  rewrite H1 in H2.
  pose (proj1 (proj2 THash_not_eq) H2).
  inversion f.
  intro.
  rewrite H1 in H2.
  pose (proj2 (proj2 THash_not_eq) H2).
  inversion f.
  intro.
  assert (forall x : a, φ x ∧# p = #). intro.
  pose (andHash_is_hash H).
  elim o. intro.
  pose (existsHashDef3' H0 x).
  pose (proj2 (andHashDef1 p)).
  replace (# ∧# p = #) with
    (φ x ∧# p = #) in e0 by now (rewrite (eq_sym e)).
  exact e0.
  intro.
  rewrite H0.
  exact (proj1 (andHashDef1 (φ x))).
  exact (eq_sym (existsHashDef3 H0)).
Qed.

Lemma existsHash_andHash_existsHash_andHash :
  forall {a b : Set}
         (m : b -> T#)
         (n : a -> b -> T#)
         (o : a -> T#),
    (∃# (fun x : a => (∃# (fun y : b => m y ∧# n x y)) ∧# o x)) =
      (∃# (fun y : b => m y ∧# (∃# (fun x : a => n x y ∧# o x)))).
Proof.
  intros.
  case_eq (∃# (fun x : a => (∃# (fun y : b => m y ∧# n x y)) ∧# o x)).
  intros.
  pose (existsHashDef1' H).
  elim e. intros.
  rewrite (andHash_existsHash_comm (fun y : b => m y ∧# n x y)) in H0.
  pose (existsHashDef1' H0).
  elim e0. intros.
  pose (andHash_is_true H1).
  pose (andHash_is_true (proj1 a0)).
  assert (exists (x1 : a), n x1 x0 ∧# o x1 = ⊤#).
  pose andHashDef3.
  replace (⊤# ∧# ⊤# = ⊤#) with (n x x0 ∧# ⊤# = ⊤#) in e1 by
      now (rewrite (proj2 a1)).
  replace  (n x x0 ∧# ⊤# = ⊤#) with (n x x0 ∧# o x = ⊤#) in e1 by
      now (rewrite (proj2 a0)).
  exact (ex_intro (fun x1 : a => n x1 x0 ∧# o x1 = ⊤#) x e1).
  pose (existsHashDef1 H2).
  pose andHashDef3.
  replace (⊤# ∧# ⊤# = ⊤#) with
    (⊤# ∧# (∃# (fun x1 : a => n x1 x0 ∧# o x1)) = ⊤#) in e2 by
      now (rewrite (eq_sym e1)).
  replace (⊤# ∧# (∃# (fun x1 : a => n x1 x0 ∧# o x1)) = ⊤#) with
    (m x0 ∧# (∃# (fun x1 : a => n x1 x0 ∧# o x1)) = ⊤#) in e2 by
      now (rewrite (eq_sym (proj1 a1))).
  exact (eq_sym
           (existsHashDef1
              (ex_intro
                 (fun y : b => m y ∧# (∃# (fun x1 : a => n x1 y ∧# o x1)) = ⊤#)
                 x0 e2))).
  intro.
  case_eq (∃# (fun y : b => m y ∧# (∃# (fun x : a => n x y ∧# o x)))).
  intro.
  pose (existsHashDef1' H0).
  elim e. intros.
  pose (andHash_is_true H1).
  pose (existsHashDef1' (proj2 a0)).
  elim e0. intros.
  pose (andHash_is_true H2).
  pose andHashDef3.
  replace (⊤# ∧# ⊤#) with (m x ∧# ⊤#) in e1 by
      now (rewrite (eq_sym (proj1 a0))).
  replace (m x ∧# ⊤#) with (m x ∧# n x0 x) in e1 by
      now (rewrite (eq_sym (proj1 a1))).
  pose (existsHashDef1 (ex_intro (fun y : b => m y ∧# n x0 y = ⊤#) x e1)).
  pose andHashDef3.
  replace (⊤# ∧# ⊤#) with ((∃# (fun y : b => m y ∧# n x0 y)) ∧# ⊤#) in e3 by
      now (rewrite (eq_sym e2)).
  replace ((∃# (fun y : b => m y ∧# n x0 y)) ∧# ⊤#) with
    ((∃# (fun y : b => m y ∧# n x0 y)) ∧# o x0) in e3 by
      now (rewrite (eq_sym (proj2 a1))).
  rewrite (existsHashDef1
             (ex_intro
                (fun x : a => (∃# (fun y : b => m y ∧# n x y)) ∧# o x = ⊤#)
                x0 e3)) in H.
  exact (eq_sym H).
  trivial.
  intro.
  assert (forall x : a, (∃# (fun y : b => m y ∧# n x y)) ∧# o x = #).
  intro.
  pose (existsHashDef3' H0).
  case_eq (∃# (fun y : b => m y ∧# n x y)). intro.
  pose (existsHashDef1' H1).
  elim e0. intros.
  pose (andHash_is_hash (e x0)). elim o0. intro.
  rewrite H3 in H2.
  rewrite (proj2 (andHashDef1 (n x x0))) in H2.
  pose (proj1 (proj2 THash_not_eq) H2).
  inversion f.
  intro.
  pose (existsHashDef3' H3 x).
  rewrite (eq_sym (proj2 (andHash_is_true H2))).
  exact e1.
  intro.
  pose (existsHashDef2' H1).
  elim (proj1 a0). intros.
  pose (andHash_is_hash (e x0)). elim o0. intro.
  rewrite H3 in H2.
  rewrite (proj2 (andHashDef1 (n x x0))) in H2.
  pose (proj2 (proj2 THash_not_eq) H2).
  inversion f.
  intro.
  elim (andHash_is_hash (existsHashDef3' H3 x)). intro.
  rewrite H4 in H2.
  rewrite (proj1 (andHashDef1 (m x0))) in H2.
  pose (proj2 (proj2 THash_not_eq) H2).
  inversion f.
  intro.
  rewrite H4.
  apply (proj1 (andHashDef1 ⊥#)).
  intro.
  apply (proj2 (andHashDef1 (o x))).
  pose (existsHashDef2' H).
  elim (proj1 a0). intros.
  elim (andHash_is_hash (H1 x)). intro.
  elim (proj1 (andHash_is_false2 H2)).
  rewrite H3.
  intro.
  pose (proj1 (proj2 THash_not_eq) H4).
  inversion f.
  intro.
  rewrite H4 in H3.
  exact H3.
  intro.
  rewrite H3 in H2.
  rewrite (proj1 (andHashDef1 (∃# (fun y : b => m y ∧# n x y)))) in H2.
  exact (eq_sym H2).
  intro.
  assert (forall (y : b), m y ∧#  (∃# (fun x : a => n x y ∧# o x)) = #). intro.
  case_eq (m y). intro.
  assert (forall (x : a), n x y ∧# o x = #). intro.
  pose (existsHashDef3' H x).
  pose (andHash_is_hash e).
  elim o0. intro.
  pose (existsHashDef3' H1 y).
  pose (andHash_is_hash e0).
  elim o1. intro.
  rewrite H0 in H2.
  pose (proj1 (proj2 THash_not_eq) (eq_sym H2)).
  inversion f.
  intro.
  rewrite H2.
  exact (proj2 (andHashDef1 (o x))).
  intro.
  rewrite H1.
  exact (proj1 (andHashDef1 (n x y))).
  rewrite (existsHashDef3 H1).
  exact (proj1 (andHashDef1 ⊤#)).
  intro.
  assert (forall (x : a), n x y ∧# o x = #). intro.
  pose (existsHashDef3' H x).
  pose (andHash_is_hash e).
  elim o0. intro.
  pose (existsHashDef3' H1 y).
  pose (andHash_is_hash e0).
  elim o1. intro.
  rewrite H0 in H2.
  pose (proj2 (proj2 THash_not_eq) (eq_sym H2)).
  inversion f.
  intro.
  rewrite H2.
  exact (proj2 (andHashDef1 (o x))).
  intro.
  rewrite H1.
  exact (proj1 (andHashDef1 (n x y))).
  rewrite (existsHashDef3 H1).
  exact (proj1 (andHashDef1 ⊥#)).
  intro.
  exact (proj2 (andHashDef1 (∃# (fun x : a => n x y ∧# o x)))).
  exact (eq_sym (existsHashDef3 H0)).
Qed.

Parameter δ : T -> T#.
(* Notation "δ " := δ (at level 85, right associativity). *)
Axiom δDef : δ ⊤ = ⊤# /\ δ ⊥ = #.

Lemma δ_true : forall {x : T}, δ x = ⊤# -> x = true.
Proof.
  intros.
  case_eq x. intro.
  trivial.
  intro.
  rewrite H0 in H.
  rewrite (proj2 δDef) in H.
  pose (proj1 (proj2 THash_not_eq) H).
  inversion f.
Qed.

Parameter eqHash : forall {a : Set}, a -> a -> T.
Notation "x ≡ y" := (eqHash x y) (at level 80, right associativity).
Axiom eqHashRefl1 : forall {a : Set} {x y : a}, x = y -> (x ≡ y) = ⊤.
Axiom eqHashRefl2 : forall {a : Set} {x y : a}, (x ≡ y) = ⊤ -> x = y.

Lemma eqHashRefl1_converse :
  forall {a : Set} {x y : a}, ~ (x = y) -> (x ≡ y) = ⊥.
Proof.
  intros.
  case_eq (x ≡ y). intro.
  pose (H (eqHashRefl2 H0)).
  inversion f.
  trivial.
Qed.

Lemma eqHashRefl2_converse :
  forall {a : Set} {x y : a}, (x ≡ y) = ⊥ -> ~ (x = y).
Proof.
  intros.
  intro.
  pose (eqHashRefl1 H0).
  rewrite e in H.
  exact (T_not_eq H).
Qed.

Lemma eqHash_comm : forall {a : Set} (x y : a), (x ≡ y) = (y ≡ x).
Proof.
  intros.
  case_eq (x ≡ y).
  case_eq (y ≡ x).
  intros. trivial.
  intros.
  pose (eqHashRefl2_converse H).
  pose (eqHashRefl2 H0).
  pose (n (eq_sym e)).
  inversion f.
  intro.
  case_eq (eqHash y x).
  intro.
  pose (eqHashRefl2_converse H).
  pose (eqHashRefl2 H0).
  pose (n (eq_sym e)).
  inversion f.
  intro. trivial.
Qed.

Lemma δElim :
  forall {a : Set} (v : a) (φ : a -> T#),
    (∃# (fun (x : a) => δ (x ≡ v) ∧# φ x)) = φ v.
Proof.
  intros.
  case_eq (φ v).
  intro. apply eq_sym in H.
  pose andHashDef3.
  replace (⊤# ∧# ⊤# = ⊤#) with (⊤# ∧# φ v = ⊤#) in e by now (rewrite H).
  pose (proj1 δDef).
  replace (δ ⊤ = ⊤#) with (δ (v ≡ v) = ⊤#) in e0 by
      now (rewrite (eq_sym (eqHashRefl1 (eq_refl v)))).
  apply eq_sym in e0.
  replace (⊤# ∧# φ v = ⊤#) with (δ (v ≡ v) ∧# φ v = ⊤#) in e by
      now (rewrite e0).
  pose (ex_intro (fun x : a => δ (x ≡ v) ∧# φ x = ⊤#) v e).
  exact (existsHashDef1 e1).
  intro. apply eq_sym in H.
  pose (proj1 andHashDef2).
  replace (⊤# ∧# ⊥# = ⊥#) with (⊤# ∧# φ v = ⊥#) in e by now (rewrite H).
  pose (proj1 δDef).
  replace (δ ⊤ = ⊤#) with (δ (v ≡ v) = ⊤#) in e0 by
      now (rewrite (eq_sym (eqHashRefl1 (eq_refl v)))).
  apply eq_sym in e0.
  replace (⊤# ∧# φ v = ⊥#) with (δ (v ≡ v) ∧# φ v = ⊥#) in e by
      now (rewrite e0).
  pose (ex_intro (fun x : a => δ (x ≡ v) ∧# φ x = ⊥#) v e).
  assert (~ (exists x : a, δ (x ≡ v) ∧# φ x = ⊤#)).
  intro.
  elim H0.
  intros.
  pose (andHash_is_true H1).
  pose (proj1 a0).
  pose (eqHashRefl2 (δ_true e2)).
  pose (proj2 a0).
  rewrite e3 in e4.
  rewrite e4 in H.
  exact (proj1 THash_not_eq (eq_sym H)).
  exact (existsHashDef2 (conj e1 H0)).
  intros.
  assert (forall (x : a), δ (x ≡ v) ∧# φ x = #).
  intro.
  case_eq (eqHash x v). intro.
  rewrite (eqHashRefl2 H0).
  rewrite H.
  rewrite (proj1 (andHashDef1 (δ ⊤))).
  trivial.
  intro.
  rewrite (proj2 δDef).
  rewrite (proj2 (andHashDef1 (φ x))).
  trivial.
  exact (existsHashDef3 H0).
Qed.

(* Monadic stuff. *)

(* Left Identity *)
Definition monad_left_id
  (m : Set -> Set)
  (eta : forall {a : Set}, a -> m a)
  (bind : forall {a b : Set}, m a -> (a -> m b) -> m b) :=
  forall {a b : Set} (x : a) (k : a -> m b), bind (eta x) k = k x.

(* Right Identity *)
Definition monad_right_id
  (m : Set -> Set)
  (eta : forall {a : Set}, a -> m a)
  (bind : forall {a b : Set}, m a -> (a -> m b) -> m b) :=
  forall {a : Set} (m' : m a), bind m' eta = m'.

(* Associativity *)
Definition monad_assoc
  (m : Set -> Set)
  (bind : forall {a b : Set}, m a -> (a -> m b) -> m b) :=
  forall {a b c : Set} (m' : m a) (n : a -> m b) (o : b -> m c),
    bind (bind m' n) o = bind m' (fun x => bind (n x) o).

(* All three *)
Definition monad
  (m : Set -> Set)
  (eta : forall (a : Set), a -> m a)
  (bind : forall (a b : Set), m a -> (a -> m b) -> m b) :=
  monad_left_id m eta bind /\ monad_right_id m eta bind /\ monad_assoc m bind.

(* The functor S#, defined as S# α = α -> t#. *)
Definition SHash (a : Set) := a -> THash.
Notation "S#" := SHash.
Definition etaHash (a : Set) (x : a) : S# a := fun y : a => δ (y ≡ x).
Notation "η#" := etaHash.
Definition bindHash (a b : Set) (m : SHash a) (k : a -> SHash b) : SHash b :=
  fun y : b => (∃# (fun x : a => m x ∧# k x y)).
Notation "⋆#" := bindHash.
Notation "m ⋆# k" := (bindHash m k) (at level 190, left associativity).

(* We need functional extensionality (a.k.a. η-expansion). *)
Axiom functional_extensionality: forall {a b} (f g : a -> b),
    (forall x, f x = g x) -> f = g.

(* The grand finale! *)
Theorem SHash_is_a_monad : monad S# η# ⋆#.
Proof.
  split.
  unfold monad_left_id. unfold bindHash. unfold etaHash.
  intros.
  pose (functional_extensionality
          (fun y : b => ∃# (fun x0 : a => δ (x0 ≡ x) ∧# k x0 y))
          (k x)).
  assert (forall x0 : b,
             (fun y : b =>
                ∃# (fun x1 : a => (δ (x1 ≡ x)) ∧# k x1 y)) x0 = k x x0).
  intro.
  rewrite (δElim x (fun x' : a => k x' x0)). trivial.
  exact (e H).
  split.
  unfold monad_right_id. unfold bindHash. unfold etaHash.
  intros.
  pose (functional_extensionality
          (fun y : a => ∃# (fun x : a => m' x ∧# δ (y ≡ x)))
          m').
  assert (forall x : a,
             (∃# (fun x0 : a => m' x0 ∧# δ (x ≡ x0))) = m' x).
  intro.
  assert
    ((fun x0 : a => m' x0 ∧# δ (x ≡ x0)) = (fun x0 : a => δ (x0 ≡ x) ∧# m' x0)).
  pose (functional_extensionality
          (fun x0 : a => m' x0 ∧# δ (x ≡ x0))
          (fun x0 : a => δ (x0 ≡ x) ∧# m' x0)).
  assert (forall x0 : a, m' x0 ∧# δ (x ≡ x0) = δ (x0 ≡ x) ∧# m' x0).
  intro.
  rewrite (eqHash_comm x x0).
  exact (andHash_comm (m' x0) (δ (x0 ≡ x))).
  exact (e0 H).
  rewrite H.
  rewrite (δElim x m'). trivial.
  exact (e H).
  unfold monad_assoc. unfold bindHash.
  intros.
  pose (functional_extensionality
          (fun y : c =>
             ∃# (fun x : b => (∃# (fun x0 : a => m' x0 ∧# n x0 x)) ∧# o x y))
          (fun y : c =>
             ∃# (fun x : a => m' x ∧# (∃# (fun x0 : b => n x x0 ∧# o x0 y))))).
  assert (forall x : c,
             (∃# (fun x0 : b =>
                   (∃# (fun x1 : a => m' x1 ∧# n x1 x0)) ∧# (o x0 x))) =
               ∃# (fun x0 : a =>
                     m' x0 ∧# (∃# (fun x1 : b => n x0 x1 ∧# o x1 x)))).
  intro.
  exact (existsHash_andHash_existsHash_andHash
           m' (fun x y => n y x) (fun x1 => o x1 x)).
  apply functional_extensionality. intro.
  exact (existsHash_andHash_existsHash_andHash
           m' (fun x y => n y x) (fun x1 => o x1 x)).
Qed.
