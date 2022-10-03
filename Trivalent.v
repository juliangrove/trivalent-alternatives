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
Axiom existsHashDef2 : forall (a : Set) (k : a -> THash), ((exists (x : a), k x = falseHash) /\ not (exists (x : a), k x = trueHash)) -> existsHash a k = falseHash.
Axiom existsHashDef3 : forall (a : Set) (k : a -> THash), (forall (x : a), k x = hash) -> existsHash a k = hash.

Axiom andHash : THash -> THash -> THash.
Axiom andHashDef1 : forall (x : THash), andHash x hash = hash /\ andHash hash x = hash.
Axiom andHashDef2 : andHash trueHash falseHash = falseHash /\ andHash falseHash trueHash = falseHash /\ andHash falseHash falseHash = falseHash.
Axiom andHashDef3 : andHash trueHash trueHash = trueHash.

Lemma and_is_true : forall (x  y : THash), andHash x y = trueHash -> x = trueHash /\ y = trueHash.
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

Lemma and_is_hash : forall (x  y : THash), andHash x y = hash -> x = hash \/ y = hash.
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

Theorem substTerm : forall (a : Set) (v : a) (phi : a -> THash), existsHash a (fun (x : a) => andHash (delt (eqHash a x v)) (phi x)) = phi v.
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
  pose (ex_intro (fun x : a =>
     andHash (delt (eqHash a x v)) (phi x) = trueHash) v e).
  exact (existsHashDef1 a (fun x : a =>
                             andHash (delt (eqHash a x v)) (phi x)) e1).
  intro. apply eq_sym in H.
  pose (proj1 andHashDef2).
  replace (andHash trueHash falseHash = falseHash) with (andHash trueHash (phi v) = falseHash) in e by now (rewrite H).
  pose (proj1 deltDef).
  replace (delt true = trueHash) with (delt (eqHash a v v) = trueHash) in e0 by now (rewrite (eq_sym (eqHashRefl1 a v v eq_refl))).
  apply eq_sym in e0.
  replace (andHash trueHash (phi v) = falseHash) with (andHash (delt (eqHash a v v)) (phi v) = falseHash) in e by now (rewrite e0).
  pose (ex_intro (fun x : a =>
                    andHash (delt (eqHash a x v)) (phi x) = falseHash) v e).
  assert (not (exists x : a, andHash (delt (eqHash a x v)) (phi x) = trueHash)).
  intro.
  elim H0.
  intros.
  pose (and_is_true (delt (eqHash a x v)) (phi x) H1).
  pose (proj1 a0).
  pose (eqHashRefl2 a x v (delt_true (eqHash a x v) e2)).
  pose (proj2 a0).
  rewrite e3 in e4.
  rewrite e4 in H.
  exact (proj1 THash_not_eq (eq_sym H)).
  exact (existsHashDef2 a (fun x : a =>
                             andHash (delt (eqHash a x v)) (phi x)) (conj e1 H0)).
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
  exact (existsHashDef3 a (fun x : a =>
                             andHash (delt (eqHash a x v)) (phi x)) H0).
Qed.
