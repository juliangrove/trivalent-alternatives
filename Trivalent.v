Inductive T :=
| true : T
| false : T.

Axiom T_not_eq : not (true = false).

Inductive THash :=
| trueHash : THash
| falseHash : THash
| hash : THash.

Axiom THash_not_eq : not (trueHash = falseHash) /\ not (hash = trueHash) /\ not (hash = falseHash).

Axiom existsHash : forall (a : Set), (a -> THash) -> THash.
Axiom existsHashDef1 : forall (a : Set) (k : a -> THash), (exists (x : a), k x = trueHash) -> existsHash a k = trueHash.
Axiom existsHashDef1' : forall (a : Set) (k : a -> THash), existsHash a k = trueHash -> (exists (x : a), k x = trueHash).
Axiom existsHashDef2 : forall (a : Set) (k : a -> THash), ((exists (x : a), k x = falseHash) /\ not (exists (x : a), k x = trueHash)) -> existsHash a k = falseHash.
Axiom existsHashDef2' : forall (a : Set) (k : a -> THash), existsHash a k = falseHash -> ((exists (x : a), k x = falseHash) /\ not (exists (x : a), k x = trueHash)).
Axiom existsHashDef3 : forall (a : Set) (k : a -> THash), (forall (x : a), k x = hash) -> existsHash a k = hash.
Axiom existsHashDef3' : forall (a : Set) (k : a -> THash), existsHash a k = hash -> (forall (x : a), k x = hash).

Lemma existsHash_comm : forall (a : Set) (b : Set) (k : a * b -> THash),
    existsHash a (fun x : a => existsHash b (fun (y : b) => k (x, y))) =
      existsHash b (fun y : b => existsHash a (fun (x : a) => k (x, y))).
Proof.
  intros.
  case_eq (existsHash a (fun x : a => existsHash b (fun (y : b) => k (x, y)))).
  intros.
  pose (existsHashDef1' a (fun x : a => existsHash b (fun y : b => k (x, y))) H).
  elim e.
  intros.
  pose (existsHashDef1' b (fun y : b => k (x, y)) H0).
  elim e0.
  intros.
  pose (existsHashDef1 a (fun x1 : a => k (x1, x0)) (ex_intro (fun (x1 : a) => k (x1, x0) = trueHash) x H1)).
  pose (existsHashDef1 b (fun y : b => existsHash a (fun x1 : a => k (x1, y))) (ex_intro (fun y : b => existsHash a (fun x1 : a => k (x1, y)) = trueHash) x0 e1)).
  exact (eq_sym e2).
  intro.
  pose (existsHashDef2' a (fun x : a => existsHash b (fun y : b => k (x, y))) H).
  elim a0.
  intros.
  elim H0.
  intros.
  pose (existsHashDef2' b (fun y : b => k (x, y)) H2).
  pose (proj1 a1).
  elim e.
  intros.
  pose (ex_intro (fun x1 : a => k (x1, x0) = falseHash) x H3).
  assert (not (exists (x1 : a), k (x1, x0) = trueHash)).
  intro.
  elim H4.
  intros.
  pose (existsHashDef1 b (fun x0 : b => k (x1, x0)) (ex_intro (fun x0 : b => k (x1, x0) = trueHash) x0 H5)).
  pose (existsHashDef1 a (fun x1 : a => existsHash b (fun x0 : b => k (x1, x0))) (ex_intro (fun x1 : a => existsHash b (fun x0 : b => k (x1, x0)) = trueHash) x1 e1)).
  rewrite H in e2.
  exact (proj1 THash_not_eq (eq_sym e2)).
  pose (ex_intro (fun x0 : b => existsHash a (fun x1 : a => k (x1, x0)) = falseHash) x0 (existsHashDef2 a (fun x1 : a => k (x1, x0)) (conj e0 H4))).
  assert (not (exists x0 : b, existsHash a (fun x1 : a => k (x1, x0)) = trueHash)).
  intro.
  elim H5.
  intros.
  pose (existsHashDef1' a (fun x2 : a => k (x2, x1)) H6).
  elim e2.
  intros.
  pose (existsHashDef1 b (fun x1 : b => k (x2, x1)) (ex_intro (fun x1 : b => k (x2, x1) = trueHash) x1 H7)).
  pose (existsHashDef1 a (fun x2 : a => existsHash b (fun x1 : b => k (x2, x1))) (ex_intro (fun x2 : a => existsHash b (fun x1 : b => k (x2, x1)) = trueHash) x2 e3)).
  rewrite H in e4.
  exact (proj1 THash_not_eq (eq_sym e4)).
  exact (eq_sym (existsHashDef2 b (fun y : b => existsHash a (fun x1 : a => k (x1, y))) (conj e1 H5))).
  intro.
  assert (forall y : b, existsHash a (fun x : a => k (x, y)) = hash).
  intro.
  assert (forall x : a, k (x, y) = hash).
  intro.
  pose (existsHashDef3' a (fun x : a => existsHash b (fun y : b => k (x, y))) H x).
  exact (existsHashDef3' b (fun y : b => k (x, y)) e y).
  exact (existsHashDef3 a (fun x : a => k (x, y)) H0).
  exact (eq_sym (existsHashDef3 b (fun y : b => existsHash a (fun x : a => k (x, y))) H0)).
Qed.
  
Axiom andHash : THash -> THash -> THash.
Axiom andHashDef1 : forall (x : THash), andHash x hash = hash /\ andHash hash x = hash.
Axiom andHashDef2 : andHash trueHash falseHash = falseHash /\ andHash falseHash trueHash = falseHash /\ andHash falseHash falseHash = falseHash.
Axiom andHashDef3 : andHash trueHash trueHash = trueHash.

Lemma andHash_is_true : forall (x  y : THash), andHash x y = trueHash -> x = trueHash /\ y = trueHash.
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

Lemma andHash_is_hash : forall (x y : THash), andHash x y = hash -> x = hash \/ y = hash.
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
   
Lemma andHash_assoc : forall (x y z : THash), andHash x (andHash y z) = andHash (andHash x y) z.
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
 
Axiom delt : T -> THash.
Axiom deltDef : delt true = trueHash /\ delt false = hash.

Lemma delt_inj : forall (x y : T), delt x = delt y -> x = y.
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

Lemma delt_true : forall (x : T), delt x = trueHash -> x = true.
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

Axiom eqHash : forall (a : Set), a -> a -> T.
Axiom eqHashRefl1 : forall (a : Set) (x y : a), x = y -> eqHash a x y = true.
Axiom eqHashRefl2 : forall (a : Set) (x y : a), eqHash a x y = true -> x = y.

Theorem delt_elim : forall (a : Set) (v : a) (phi : a -> THash), existsHash a (fun (x : a) => andHash (delt (eqHash a x v)) (phi x)) = phi v.
Proof.
  intros.
  case_eq (phi v).
  intro. apply eq_sym in H.
  pose andHashDef3.
  replace (andHash trueHash trueHash = trueHash) with (andHash trueHash (phi v) = trueHash) in e by now (rewrite H).
  pose (proj1 deltDef).
  replace (delt true = trueHash) with (delt (eqHash a v v) = trueHash) in e0 by now (rewrite (eq_sym (eqHashRefl1 a v v eq_refl))).
  apply eq_sym in e0.
  replace (andHash trueHash (phi v) = trueHash) with (andHash (delt (eqHash a v v)) (phi v) = trueHash) in e by now (rewrite e0).
  pose (ex_intro (fun x : a => andHash (delt (eqHash a x v)) (phi x) = trueHash) v e).
  exact (existsHashDef1 a (fun x : a => andHash (delt (eqHash a x v)) (phi x)) e1).
  intro. apply eq_sym in H.
  pose (proj1 andHashDef2).
  replace (andHash trueHash falseHash = falseHash) with (andHash trueHash (phi v) = falseHash) in e by now (rewrite H).
  pose (proj1 deltDef).
  replace (delt true = trueHash) with (delt (eqHash a v v) = trueHash) in e0 by now (rewrite (eq_sym (eqHashRefl1 a v v eq_refl))).
  apply eq_sym in e0.
  replace (andHash trueHash (phi v) = falseHash) with (andHash (delt (eqHash a v v)) (phi v) = falseHash) in e by now (rewrite e0).
  pose (ex_intro (fun x : a => andHash (delt (eqHash a x v)) (phi x) = falseHash) v e).
  assert (not (exists x : a, andHash (delt (eqHash a x v)) (phi x) = trueHash)).
  intro.
  elim H0.
  intros.
  pose (andHash_is_true (delt (eqHash a x v)) (phi x) H1).
  pose (proj1 a0).
  pose (eqHashRefl2 a x v (delt_true (eqHash a x v) e2)).
  pose (proj2 a0).
  rewrite e3 in e4.
  rewrite e4 in H.
  exact (proj1 THash_not_eq (eq_sym H)).
  exact (existsHashDef2 a (fun x : a => andHash (delt (eqHash a x v)) (phi x)) (conj e1 H0)).
  intros.
  assert (forall (x : a), andHash (delt (eqHash a x v)) (phi x) = hash).
  intro.
  case_eq (eqHash a x v). intro.
  rewrite (eqHashRefl2 a x v H0).
  rewrite H.
  rewrite (proj1 (andHashDef1 (delt true))).
  trivial.
  intro.
  rewrite (proj2 deltDef).
  rewrite (proj2 (andHashDef1 (phi x))).
  trivial.
  exact (existsHashDef3 a (fun x : a => andHash (delt (eqHash a x v)) (phi x)) H0).
Qed.
