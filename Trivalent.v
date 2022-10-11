(* Boolean t. *)
Inductive T :=
| true : T
| false : T.

Definition T_elim {a : Type} (p : T) (v1 v2 : a) : a :=
  match p with
  | true => v1
  | false => v2
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

Definition THash_elim {a : Type} (p : THash) (v1 v2 v3 : a) : a :=
  match p with
  | trueHash => v1
  | falseHash => v2
  | hash => v3
  end.

(* Convienent to have. *)
Theorem THash_not_eq : ~ (trueHash = falseHash) /\
                         ~ (hash = trueHash) /\
                         ~ (hash = falseHash).
Proof.
  split.
  intro.
  pose (eq_refl (THash_elim trueHash unit False unit)).
  replace (THash_elim trueHash unit False unit =
             THash_elim trueHash unit False unit) with
    (THash_elim trueHash unit False unit =
       THash_elim falseHash unit False unit)
    in e by now (rewrite H).
  pose tt.
  unfold THash_elim in e.
  rewrite e in u.
  exact u.
  split.
  intro.
  pose (eq_refl (THash_elim trueHash unit unit False)).
  replace (THash_elim trueHash unit unit False =
             THash_elim trueHash unit unit False) with
    (THash_elim trueHash unit unit False =
       THash_elim hash unit unit False)
    in e by now (rewrite H).
  pose tt.
  unfold THash_elim in e.
  rewrite e in u.
  exact u.
  intro.
  pose (eq_refl (THash_elim falseHash unit unit False)).
  replace (THash_elim falseHash unit unit False =
             THash_elim falseHash unit unit False) with
    (THash_elim falseHash unit unit False =
       THash_elim hash unit unit False)
    in e by now (rewrite H).
  pose tt.
  unfold THash_elim in e.
  rewrite e in u.
  exact u.
Qed.

(* The ``charitable'' trivalent existential quantifier, ∃#. *)
Parameter existsHash : forall {a : Set}, (a -> THash) -> THash.
Axiom existsHashDef1 : forall {a : Set} {k : a -> THash},
    (exists (x : a), k x = trueHash) -> existsHash k = trueHash.
Axiom existsHashDef1' : forall {a : Set} {k : a -> THash},
    existsHash k = trueHash -> (exists (x : a), k x = trueHash).
Axiom existsHashDef2 : forall {a : Set} {k : a -> THash},
    ((exists (x : a), k x = falseHash) /\ ~ (exists (x : a), k x = trueHash)) ->
    existsHash k = falseHash.
Axiom existsHashDef2' : forall {a : Set} {k : a -> THash},
    existsHash k = falseHash ->
    (exists (x : a), k x = falseHash) /\ ~ (exists (x : a), k x = trueHash).
Axiom existsHashDef3 : forall {a : Set} {k : a -> THash},
    (forall (x : a), k x = hash) -> existsHash k = hash.
Axiom existsHashDef3' : forall {a : Set} {k : a -> THash},
    existsHash k = hash -> (forall (x : a), k x = hash).

Lemma existsHash_comm : forall {a : Set} {b : Set} {k : a * b -> THash},
    existsHash (fun x : a => existsHash (fun (y : b) => k (x, y))) =
      existsHash (fun y : b => existsHash (fun (x : a) => k (x, y))).
Proof.
  intros.
  case_eq (existsHash (fun x : a => existsHash (fun (y : b) => k (x, y)))).
  intros.
  pose (existsHashDef1' H).
  elim e.
  intros.
  pose (existsHashDef1' H0).
  elim e0.
  intros.
  pose (existsHashDef1 (ex_intro (fun (x1 : a) => k (x1, x0) = trueHash) x H1)).
  pose (existsHashDef1
          (ex_intro (fun y : b =>
                       existsHash (fun x1 : a => k (x1, y)) = trueHash) x0 e1)).
  exact (eq_sym e2).
  intro.
  pose (existsHashDef2' H).
  elim a0.
  intros.
  elim H0.
  intros.
  pose (existsHashDef2' H2).
  pose (proj1 a1).
  elim e.
  intros.
  pose (ex_intro (fun x1 : a => k (x1, x0) = falseHash) x H3).
  assert (not (exists (x1 : a), k (x1, x0) = trueHash)).
  intro.
  elim H4.
  intros.
  pose (existsHashDef1 (ex_intro (fun x0 : b => k (x1, x0) = trueHash) x0 H5)).
  pose (existsHashDef1
          (ex_intro (fun x1 : a =>
                       existsHash (fun x0 : b =>
                                     k (x1, x0)) = trueHash) x1 e1)).
  rewrite H in e2.
  exact (proj1 THash_not_eq (eq_sym e2)).
  pose (ex_intro (fun x0 : b =>
                    existsHash (fun x1 : a => k (x1, x0)) = falseHash)
          x0 (existsHashDef2 (conj e0 H4))).
  assert (not
            (exists x0 : b, existsHash (fun x1 : a => k (x1, x0)) = trueHash)).
  intro.
  elim H5.
  intros.
  pose (existsHashDef1' H6).
  elim e2.
  intros.
  pose (existsHashDef1 (ex_intro (fun x1 : b => k (x2, x1) = trueHash) x1 H7)).
  pose (existsHashDef1
          (ex_intro (fun x2 : a =>
                       existsHash (fun x1 :
                                     b => k (x2, x1)) = trueHash) x2 e3)).
  rewrite H in e4.
  exact (proj1 THash_not_eq (eq_sym e4)).
  exact (eq_sym (existsHashDef2  (conj e1 H5))).
  intro.
  assert (forall y : b, existsHash (fun x : a => k (x, y)) = hash).
  intro.
  assert (forall x : a, k (x, y) = hash).
  intro.
  pose (existsHashDef3' H x).
  exact (existsHashDef3' e y).
  exact (existsHashDef3 H0).
  exact (eq_sym (existsHashDef3 H0)).
Qed.

(* Weak Kleene ∧, i.e., ∧#. *)
Parameter andHash : THash -> THash -> THash.
Axiom andHashDef1 : forall (x : THash),
    andHash x hash = hash /\ andHash hash x = hash.
Axiom andHashDef2 : andHash trueHash falseHash = falseHash /\
                      andHash falseHash trueHash = falseHash /\
                      andHash falseHash falseHash = falseHash.
Axiom andHashDef3 : andHash trueHash trueHash = trueHash.

Lemma andHash_comm : forall (x y : THash), andHash x y = andHash y x.
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
  rewrite (proj1 (andHashDef1 trueHash)).
  rewrite (proj2 (andHashDef1 trueHash)).
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
  rewrite (proj1 (andHashDef1 falseHash)).
  rewrite (proj2 (andHashDef1 falseHash)).
  trivial.
  intro.
  case_eq y.
  intro.
  rewrite (proj1 (andHashDef1 trueHash)).
  rewrite (proj2 (andHashDef1 trueHash)).
  trivial.
  intro.
  rewrite (proj1 (andHashDef1 falseHash)).
  rewrite (proj2 (andHashDef1 falseHash)).
  trivial.
  intro.
  trivial.
Qed.
  
Lemma andHash_assoc : forall (x y z : THash),
    andHash x (andHash y z) = andHash (andHash x y) z.
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
  repeat rewrite (proj1 (andHashDef1 trueHash)). trivial.
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
  repeat rewrite (proj1 (andHashDef1 falseHash)).
  rewrite (proj1 (andHashDef1 trueHash)). trivial.
  intros.
  case_eq z.
  intros.
  rewrite (proj1 (andHashDef1 trueHash)).
  repeat rewrite (proj2 (andHashDef1 trueHash)).
  rewrite (proj1 (andHashDef1 trueHash)). trivial.
  intro.
  rewrite (proj2 (andHashDef1 falseHash)).
  rewrite (proj1 (andHashDef1 trueHash)).
  rewrite (proj2 (andHashDef1 falseHash)). trivial.
  intro.
  rewrite (proj2 (andHashDef1 hash)).
  rewrite (proj1 (andHashDef1 trueHash)).
  rewrite (proj2 (andHashDef1 hash)). trivial.
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
  rewrite (proj1 (andHashDef1 trueHash)).
  rewrite (proj1 (proj2 andHashDef2)).
  repeat rewrite (proj1 (andHashDef1 falseHash)). trivial.
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
  repeat rewrite (proj1 (andHashDef1 falseHash)). trivial.
  intros.
  case_eq z.
  intro.
  rewrite (proj1 (andHashDef1 falseHash)).
  repeat rewrite (proj2 (andHashDef1 trueHash)).
  rewrite (proj1 (andHashDef1 falseHash)). trivial.
  intro.
  rewrite (proj1 (andHashDef1 falseHash)).
  rewrite (proj2 (andHashDef1 falseHash)).
  rewrite (proj1 (andHashDef1 falseHash)). trivial.
  intro.
  rewrite (proj1 (andHashDef1 hash)).
  repeat rewrite (proj1 (andHashDef1 falseHash)).
  rewrite (proj1 (andHashDef1 hash)). trivial.
  case_eq y.
  case_eq z.
  intros.
  rewrite andHashDef3.
  repeat rewrite (proj2 (andHashDef1 trueHash)). trivial.
  intros.
  rewrite (proj1 andHashDef2).
  rewrite (proj2 (andHashDef1 trueHash)). trivial.
  intros.
  rewrite (proj2 (andHashDef1 trueHash)).
  rewrite (proj1 (andHashDef1 trueHash)). trivial.
  case_eq z.
  intros.
  rewrite (proj2 (andHashDef1 falseHash)).
  rewrite (proj1 (proj2 andHashDef2)).
  rewrite (proj2 (andHashDef1 falseHash)).
  rewrite (proj2 (andHashDef1 trueHash)). trivial.
  intros.
  rewrite (proj2 (proj2 andHashDef2)).
  repeat rewrite (proj2 (andHashDef1 falseHash)). trivial.
  intros.
  rewrite (proj2 (andHashDef1 falseHash)).
  rewrite (proj1 (andHashDef1 falseHash)). trivial.
  case_eq z.
  intros.
  rewrite (proj2 (andHashDef1 trueHash)).
  repeat rewrite (proj2 (andHashDef1 hash)).
  rewrite (proj2 (andHashDef1 trueHash)). trivial.
  intros.
  rewrite (proj2 (andHashDef1 falseHash)).
  repeat rewrite (proj2 (andHashDef1 hash)).
  rewrite (proj2 (andHashDef1 falseHash)). trivial.
  intros.
  repeat rewrite (proj2 (andHashDef1 hash)). trivial.
Qed.
 
Lemma andHash_is_true : forall {x  y : THash},
    andHash x y = trueHash -> x = trueHash /\ y = trueHash.
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
  rewrite (proj1 (andHashDef1 trueHash)) in H.
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
  rewrite (proj1 (andHashDef1 falseHash)) in H.
  pose (proj1 (proj2 THash_not_eq) H).
  inversion f.
  intros.
  rewrite H0 in H.
  case_eq y.
  intros.
  rewrite H1 in H.
  rewrite (proj2 (andHashDef1 trueHash)) in H.
  pose (proj1 (proj2 THash_not_eq) H).
  inversion f.
  intros.
  rewrite H1 in H.
  rewrite (proj2 (andHashDef1 falseHash)) in H.
  pose (proj1 (proj2 THash_not_eq) H).
  inversion f.
  intros.
  rewrite H1 in H.
  rewrite (proj1 (andHashDef1 hash)) in H.
  exact (conj H H).
Qed.

Lemma andHash_is_false1 : forall {x y : THash},
    andHash x y = falseHash -> x = falseHash \/ y = falseHash.
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
  rewrite (proj1 (andHashDef1 trueHash)) in H.
  pose (proj2 (proj2 THash_not_eq) H).
  inversion f.
  intro.
  left. trivial.
  intro.
  case_eq y.
  intro.
  rewrite H0 in H.
  rewrite H1 in H.
  rewrite (proj2 (andHashDef1 trueHash)) in H.
  pose (proj2 (proj2 THash_not_eq) H).
  inversion f.
  intro.
  right. trivial.
  intro.
  rewrite H0 in H.
  rewrite H1 in H.
  rewrite (proj1 (andHashDef1 hash)) in H.
  pose (proj2 (proj2 THash_not_eq) H).
  inversion f.
Qed.

Lemma andHash_is_false2 : forall {x y : THash},
    andHash x y = falseHash ->
    (x = trueHash \/ x = falseHash) /\ (y = trueHash \/ y = falseHash).
Proof.
  assert (forall (x y : THash),
             andHash x y = falseHash -> x = trueHash \/ x = falseHash). intros.
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
 
Lemma andHash_is_hash : forall {x y : THash},
    andHash x y = hash -> x = hash \/ y = hash.
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

Parameter delt : T -> THash.
Axiom deltDef : delt true = trueHash /\ delt false = hash.

Lemma delt_inj : forall {x y : T}, delt x = delt y -> x = y.
Proof.
  intros.
  case_eq x.
  case_eq y.
  intros.
  trivial.
  intros.
  rewrite H0 in H.
  rewrite H1 in H.
  rewrite (proj1 deltDef) in H.
  rewrite (proj2 deltDef) in H.
  pose (proj1 (proj2 THash_not_eq) (eq_sym H)).
  inversion f.
  case_eq x.
  intro.
  case_eq y.
  intros.
  exact (eq_sym H2).
  intros.
  trivial.
  intros.
  case_eq y.
  intros.
  rewrite H0 in H.
  rewrite H2 in H.
  rewrite (proj1 deltDef) in H.
  rewrite (proj2 deltDef) in H.
  pose (proj1 (proj2 THash_not_eq) H).
  inversion f.
  intro.
  trivial.
Qed.

Lemma andHash_existsHash_comm : forall {a : Set} (phi : a -> THash) (p : THash),
    andHash (existsHash phi) p = existsHash (fun x : a => andHash (phi x) p).
Proof.
  intros.
  case_eq (andHash (existsHash phi) p).
  intro.
  pose (andHash_is_true H).
  pose (existsHashDef1' (proj1 a0)).
  elim e.
  intros.
  pose andHashDef3.
  replace (andHash trueHash trueHash = trueHash) with
    (andHash (phi x) trueHash = trueHash) in e0 by now (rewrite (eq_sym H0)).
  replace (andHash (phi x) trueHash = trueHash) with
    (andHash (phi x) p = trueHash) in e0 by now (rewrite (proj2 a0)).
  exact (eq_sym
           (existsHashDef1
              (ex_intro (fun x0 : a => andHash (phi x0) p = trueHash) x e0))).
  intro.
  pose (andHash_is_false1 H).
  elim o.
  intro.
  pose (existsHashDef2' H0).
  assert (exists x : a, andHash (phi x) p = falseHash).
  elim (proj1 a0).
  intros.
  case_eq p.
  intro.
  pose (proj1 (proj2 andHashDef2)).
  replace (andHash falseHash trueHash = falseHash) with
    (andHash (phi x) trueHash = falseHash) in e by now (rewrite (eq_sym H1)).
  exact (ex_intro (fun x0 : a => andHash (phi x0) trueHash = falseHash) x e).
  intro.
  pose (proj2 (proj2 andHashDef2)).
  replace (andHash falseHash falseHash = falseHash) with
    (andHash (phi x) falseHash = falseHash) in e by now (rewrite (eq_sym H1)).
  exact (ex_intro (fun x0 : a => andHash (phi x0) falseHash = falseHash) x e).
  intro.
  pose H.
  rewrite H2 in e.
  rewrite (proj1 (andHashDef1 (existsHash phi))) in e.
  pose (proj2 (proj2 THash_not_eq) e).
  inversion f.
  assert (~ (exists x : a, andHash (phi x) p = trueHash)).
  intro.
  elim H2.
  intros.
  exact (proj2 a0 (ex_intro
                     (fun x => phi x = trueHash)
                     x (proj1 (andHash_is_true H3)))).
  exact (eq_sym (existsHashDef2 (conj H1 H2))).
  intro.
  rewrite H0.
  case_eq (existsHash phi). intro.
  pose (existsHashDef1' H1).
  elim e. intros.
  pose (proj1 andHashDef2).
  rewrite (eq_sym H2) in e0.
  pose (ex_intro (fun x : a => andHash (phi x) falseHash = falseHash) x e0).
  assert (~ exists x : a, andHash (phi x) falseHash = trueHash). intro.
  elim H3. intros.
  exact (proj1 THash_not_eq
           (eq_sym (proj2 (andHash_is_true H4)))).
  exact (eq_sym (existsHashDef2 (conj e1 H3))).
  intro.
  pose (existsHashDef2' H1).
  assert (exists x : a, andHash (phi x) falseHash = falseHash).
  elim (proj1 a0). intros.
  pose (proj2 (proj2 andHashDef2)).
  replace (andHash falseHash falseHash = falseHash) with
    (andHash (phi x) falseHash = falseHash) in e by now (rewrite (eq_sym H2)).
  exact (ex_intro (fun x0 : a => andHash (phi x0) falseHash = falseHash) x e).
  assert (~ exists x : a, andHash (phi x) falseHash = trueHash). intro.
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
  assert (forall x : a, andHash (phi x) p = hash). intro.
  pose (andHash_is_hash H).
  elim o. intro.
  pose (existsHashDef3' H0 x).
  pose (proj2 (andHashDef1 p)).
  replace (andHash hash p = hash) with
    (andHash (phi x) p = hash) in e0 by now (rewrite (eq_sym e)).
  exact e0.
  intro.
  rewrite H0.
  exact (proj1 (andHashDef1 (phi x))).
  exact (eq_sym (existsHashDef3 H0)).
Qed.

Lemma existsHash_andHash_existsHash_andHash : forall {a b : Set}
                                                     (m : b -> THash)
                                                     (n : a -> b -> THash)
                                                     (o : a -> THash),
    existsHash (fun x : a =>
                  andHash (existsHash (fun y : b =>
                                         andHash (m y) (n x y))) (o x)) =
      existsHash (fun y : b =>
                    andHash (m y) (existsHash (fun x : a =>
                                                 andHash (n x y) (o x)))).
Proof.
  intros.
  case_eq (existsHash (fun x : a =>
                         andHash (existsHash (fun y : b =>
                                                andHash (m y)
                                                  (n x y))) (o x))).
  intros.
  pose (existsHashDef1' H).
  elim e. intros.
  rewrite (andHash_existsHash_comm (fun y : b =>
                                      andHash (m y) (n x y))) in H0.
  pose (existsHashDef1' H0).
  elim e0. intros.
  pose (andHash_is_true H1).
  pose (andHash_is_true (proj1 a0)).
  assert (exists (x1 : a), andHash (n x1 x0) (o x1) = trueHash).
  pose andHashDef3.
  replace (andHash trueHash trueHash = trueHash) with
    (andHash (n x x0) trueHash = trueHash) in e1 by now (rewrite (proj2 a1)).
  replace  (andHash (n x x0) trueHash = trueHash) with
    (andHash (n x x0) (o x) = trueHash) in e1 by now (rewrite (proj2 a0)).
  exact (ex_intro (fun x1 : a => andHash (n x1 x0) (o x1) = trueHash) x e1).
  pose (existsHashDef1 H2).
  pose andHashDef3.
  replace (andHash trueHash trueHash = trueHash) with
    (andHash trueHash (existsHash (fun x1 : a =>
                                     andHash (n x1 x0) (o x1))) = trueHash)
    in e2 by now (rewrite (eq_sym e1)).
  replace (andHash trueHash (existsHash (fun x1 : a =>
                                           andHash (n x1 x0)
                                             (o x1))) = trueHash) with
    (andHash (m x0) (existsHash (fun x1 : a =>
                                   andHash (n x1 x0) (o x1))) = trueHash)
    in e2 by now (rewrite (eq_sym (proj1 a1))).
  exact (eq_sym
           (existsHashDef1 (ex_intro (fun y : b =>
                                        andHash (m y)
                                          (existsHash (fun x1 : a =>
                                                         andHash (n x1 y)
                                                           (o x1))) =
                                          trueHash)
                              x0 e2))).
  intro.
  case_eq (existsHash (fun y : b =>
                         andHash (m y)
                           (existsHash (fun x : a => andHash (n x y) (o x))))).
  intro.
  pose (existsHashDef1' H0).
  elim e. intros.
  pose (andHash_is_true H1).
  pose (existsHashDef1' (proj2 a0)).
  elim e0. intros.
  pose (andHash_is_true H2).
  pose andHashDef3.
  replace (andHash trueHash) with
    (andHash (m x)) in e1 by now (rewrite (eq_sym (proj1 a0))).
  replace (andHash (m x) trueHash) with
    (andHash (m x) (n x0 x)) in e1 by now (rewrite (eq_sym (proj1 a1))).
  pose (existsHashDef1 (ex_intro (fun y : b =>
                                    andHash (m y) (n x0 y) = trueHash) x e1)).
  pose andHashDef3.
  replace (andHash trueHash) with
    (andHash (existsHash (fun y : b => andHash (m y) (n x0 y)))) in e3 by
      now (rewrite (eq_sym e2)).
  replace (andHash (existsHash (fun y : b =>
                                  andHash (m y) (n x0 y))) trueHash) with
    (andHash (existsHash (fun y : b =>
                            andHash (m y) (n x0 y))) (o x0))
    in e3 by
      now (rewrite (eq_sym (proj2 a1))).
  rewrite (existsHashDef1
             (ex_intro
                (fun x : a =>
                   andHash (existsHash
                              (fun y : b =>
                                 andHash (m y) (n x y))) (o x) = trueHash)
                x0 e3)) in H.
  exact (eq_sym H).
  trivial.
  intro.
  assert (forall x : a,
             andHash (existsHash (fun y : b =>
                                    andHash (m y) (n x y))) (o x) = hash).
  intro.
  pose (existsHashDef3' H0).
  case_eq (existsHash (fun y : b => andHash (m y) (n x y))). intro.
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
  apply (proj1 (andHashDef1 falseHash)).
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
  rewrite (proj1 (andHashDef1 (existsHash (fun y : b =>
                                             andHash (m y) (n x y))))) in H2.
  exact (eq_sym H2).
  intro.
  assert (forall (y : b),
             andHash (m y)
               (existsHash (fun x : a =>
                              andHash (n x y) (o x))) = hash). intro.
  case_eq (m y). intro.
  assert (forall (x : a), andHash (n x y) (o x) = hash). intro.
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
  exact (proj1 (andHashDef1 trueHash)).
  intro.
    assert (forall (x : a), andHash (n x y) (o x) = hash). intro.
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
  exact (proj1 (andHashDef1 falseHash)).
  intro.
  exact (proj2 (andHashDef1 (existsHash (fun x : a => andHash (n x y) (o x))))).
  exact (eq_sym (existsHashDef3 H0)).
Qed.
  
Lemma delt_true : forall {x : T}, delt x = trueHash -> x = true.
Proof.
  intros.
  case_eq x. intro.
  trivial.
  intro.
  rewrite H0 in H.
  rewrite (proj2 deltDef) in H.
  pose (proj1 (proj2 THash_not_eq) H).
  inversion f.
Qed.

Parameter eqHash : forall {a : Set}, a -> a -> T.
Axiom eqHashRefl1 : forall {a : Set} {x y : a}, x = y -> eqHash x y = true.
Axiom eqHashRefl2 : forall {a : Set} {x y : a}, eqHash x y = true -> x = y.

Lemma eqHashRefl1_converse : forall {a : Set} {x y : a},
    ~ (x = y) -> eqHash x y = false.
Proof.
  intros.
  case_eq (eqHash x y). intro.
  pose (H (eqHashRefl2 H0)).
  inversion f.
  trivial.
Qed.

Lemma eqHashRefl2_converse : forall {a : Set} {x y : a},
    eqHash x y = false -> ~ (x = y).
Proof.
  intros.
  intro.
  pose (eqHashRefl1 H0).
  rewrite e in H.
  exact (T_not_eq H).
Qed.

Lemma eqHash_comm : forall {a : Set} (x y : a), eqHash x y = eqHash y x.
Proof.
  intros.
  case_eq (eqHash x y).
  case_eq (eqHash y x).
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

Theorem delt_elim : forall {a : Set} (v : a) (phi : a -> THash),
    existsHash (fun (x : a) => andHash (delt (eqHash x v)) (phi x)) = phi v.
Proof.
  intros.
  case_eq (phi v).
  intro. apply eq_sym in H.
  pose andHashDef3.
  replace (andHash trueHash trueHash = trueHash) with
    (andHash trueHash (phi v) = trueHash) in e by now (rewrite H).
  pose (proj1 deltDef).
  replace (delt true = trueHash) with
    (delt (eqHash v v) = trueHash) in e0 by
      now (rewrite (eq_sym (eqHashRefl1 (eq_refl v)))).
  apply eq_sym in e0.
  replace (andHash trueHash (phi v) = trueHash) with
    (andHash (delt (eqHash v v)) (phi v) = trueHash) in e by now (rewrite e0).
  pose (ex_intro
          (fun x : a => andHash (delt (eqHash x v)) (phi x) = trueHash) v e).
  exact (existsHashDef1 e1).
  intro. apply eq_sym in H.
  pose (proj1 andHashDef2).
  replace (andHash trueHash falseHash = falseHash) with
    (andHash trueHash (phi v) = falseHash) in e by now (rewrite H).
  pose (proj1 deltDef).
  replace (delt true = trueHash) with
    (delt (eqHash v v) = trueHash) in e0 by
      now (rewrite (eq_sym (eqHashRefl1 (eq_refl v)))).
  apply eq_sym in e0.
  replace (andHash trueHash (phi v) = falseHash) with
    (andHash (delt (eqHash v v)) (phi v) = falseHash) in e by now (rewrite e0).
  pose (ex_intro
          (fun x : a => andHash (delt (eqHash x v)) (phi x) = falseHash) v e).
  assert (~ (exists x : a, andHash (delt (eqHash x v)) (phi x) = trueHash)).
  intro.
  elim H0.
  intros.
  pose (andHash_is_true H1).
  pose (proj1 a0).
  pose (eqHashRefl2 (delt_true e2)).
  pose (proj2 a0).
  rewrite e3 in e4.
  rewrite e4 in H.
  exact (proj1 THash_not_eq (eq_sym H)).
  exact (existsHashDef2 (conj e1 H0)).
  intros.
  assert (forall (x : a), andHash (delt (eqHash x v)) (phi x) = hash).
  intro.
  case_eq (eqHash x v). intro.
  rewrite (eqHashRefl2 H0).
  rewrite H.
  rewrite (proj1 (andHashDef1 (delt true))).
  trivial.
  intro.
  rewrite (proj2 deltDef).
  rewrite (proj2 (andHashDef1 (phi x))).
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

(* The functor S#, defined as S# α = α → t#. *)
Definition SHash (a : Set) := a -> THash.
Definition etaHash (a : Set) (x : a) : SHash a :=
  fun y : a => delt (eqHash y x).
Definition bindHash (a b : Set) (m : SHash a) (k : a -> SHash b) : SHash b :=
  fun y : b => existsHash (fun x : a => andHash (m x) (k x y)).

(* We need functional extensionality (a.k.a. η-expansion). *)
Axiom functional_extensionality: forall {a b} (f g : a -> b),
    (forall x, f x = g x) -> f = g.

(* The grand finale! *)
Theorem SHash_is_a_monad : monad SHash etaHash bindHash.
Proof.
  split.
  unfold monad_left_id. unfold bindHash. unfold etaHash.
  intros.
  pose (functional_extensionality (fun y : b =>
                                     existsHash (fun x0 : a =>
                                                   andHash (delt (eqHash x0 x))
                                                     (k x0 y))) (k x)).
  assert (forall x0 : b,
             (fun y : b =>
                existsHash (fun x1 : a =>
                              andHash (delt (eqHash x1 x)) (k x1 y))) x0 =
               k x x0).
  intro.
  rewrite (delt_elim x (fun x' : a => k x' x0)). trivial.
  exact (e H).
  split.
  unfold monad_right_id. unfold bindHash. unfold etaHash.
  intros.
  pose (functional_extensionality
          (fun y : a =>
             existsHash (fun x : a => andHash (m' x) (delt (eqHash y x)))) m').
  assert (forall x : a,
             existsHash (fun x0 : a =>
                           andHash (m' x0) (delt (eqHash x x0))) = m' x).
  intro.
  assert ((fun x0 : a => andHash (m' x0) (delt (eqHash x x0))) =
            fun x0 : a => andHash (delt (eqHash x0 x)) (m' x0)).
  pose (functional_extensionality
          (fun x0 : a =>
             andHash (m' x0)
               (delt (eqHash x x0))) (fun x0 : a =>
                                        andHash (delt (eqHash x0 x)) (m' x0))).
  assert (forall x0 : a,
             andHash (m' x0)
               (delt (eqHash x x0)) = andHash (delt (eqHash x0 x)) (m' x0)).
  intro.
  rewrite (eqHash_comm x x0).
  exact (andHash_comm (m' x0) (delt (eqHash x0 x))).
  exact (e0 H).
  rewrite H.
  rewrite (delt_elim x m'). trivial.
  exact (e H).
  unfold monad_assoc. unfold bindHash.
  intros.
  pose (functional_extensionality
          (fun y : c =>
             existsHash (fun x : b =>
                           andHash
                             (existsHash (fun x0 : a =>
                                            andHash (m' x0)
                                              (n x0 x))) (o x y)))
          (fun y : c =>
             existsHash (fun x : a =>
                           andHash (m' x)
                             (existsHash (fun x0 : b =>
                                            andHash (n x x0) (o x0 y)))))).
  assert (forall x : c,
             existsHash (fun x0 : b =>
                           andHash (existsHash (fun x1 : a =>
                                                  andHash (m' x1)
                                                    (n x1 x0))) (o x0 x)) =
               existsHash (fun x0 : a =>
                             andHash (m' x0)
                               (existsHash (fun x1 : b =>
                                              andHash (n x0 x1)
                                                (o x1 x))))).
  intro.
  exact (existsHash_andHash_existsHash_andHash
           m' (fun x y => n y x) (fun x1 => o x1 x)).
  apply functional_extensionality. intro.
  exact (existsHash_andHash_existsHash_andHash
           m' (fun x y => n y x) (fun x1 => o x1 x)).
Qed.
