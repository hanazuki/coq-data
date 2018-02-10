From mathcomp Require Import ssreflect ssrbool.
From mathcomp Require ssrnat.

Module Type TOTAL_ORDER.
  Parameters (T: Type) (leT: rel T).

  Axiom leT_refl: reflexive leT.
  Axiom leT_trans: transitive leT.
  Axiom leT_antisym: antisymmetric leT.
  Axiom leT_total: total leT.
End TOTAL_ORDER.

Module ReverseOrder(O: TOTAL_ORDER).
  Definition T := O.T.
  Definition leT x y := O.leT y x.
  Definition leT_refl := O.leT_refl.

  Lemma leT_trans: transitive leT.
  Proof. move => y z x *; exact: (@O.leT_trans y x z). Qed.

  Lemma leT_antisym: antisymmetric leT.
  Proof. move => x y; rewrite andbC; exact: O.leT_antisym. Qed.

  Lemma leT_total: total leT.
  Proof. move => x y; rewrite orbC; exact: O.leT_total. Qed.
End ReverseOrder.

Module NatOrder.
  Import ssrnat.

  Module Leq <: TOTAL_ORDER.
    Definition T := nat.
    Definition leT := leq.
    Definition leT_refl := leqnn.
    Definition leT_trans := leq_trans.
    Definition leT_antisym := anti_leq.
    Definition leT_total := leq_total.
  End Leq.

  Module Geq := ReverseOrder Leq.
End NatOrder.

Module PairOrder.
  Module ByFst(O: TOTAL_ORDER) <: TOTAL_ORDER.
    Parameter (U: Type).
    Definition T := prod O.T U.

    Definition leT (x y: T) :=
      let '(x', _) := x in
      let '(y', _) := y in
      O.leT x' y'.

    Lemma leT_refl: reflexive leT.
    Proof. move => [x ?] /= *; exact: O.leT_refl. Qed.

    Lemma leT_trans: transitive leT.
    Proof. move => [y ?] [z ?] [x ?] //= *; exact: (@O.leT_trans y z x). Qed.

  Lemma leT_antisym: antisymmetric leT.
  Proof. move => [x ?] [y ?] //=. rewrite andbC; exact: O.leT_antisym. Qed.

  Lemma leT_total: total leT.
    Lemma 
  End ByFst.
End PairOrder.
