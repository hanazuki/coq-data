From mathcomp Require Import ssreflect ssrbool.
From mathcomp Require ssrnat.

Section Orders.
  Context {T: Type} (leT: rel T).

  Class Reflexive := reflexivity: reflexive leT.
  Class Transitive := transitivity: transitive leT.
  Class Antisymmetric := antisymmetry: antisymmetric leT.
  Class Total := totality: total leT.

  Class PreOrder :=
    {
      PreOrder_Reflexive :> Reflexive;
      PreOrder_Transitive :> Transitive;
    }.

  Class PartialOrder :=
    {
      PartialOrder_PreOrder :> PreOrder;
      PartialOrder_Antisymmetric :> Antisymmetric;
    }.

  Class TotalPreOrder :=
    {
      TotalPreOrder_PreOrder :> PreOrder;
      TotalPreOrder_Total :> Total;
    }.
End Orders.

Arguments transitivity {T leT Transitive}.
Arguments antisymmetry {T leT Antisymmetric}.

Module Nat.
  Import ssrnat.

  Instance Leq: TotalPreOrder leq := {}.
  Proof.
    constructor.
    exact: leqnn.
    exact: leq_trans.
    exact: leq_total.
  Defined.
End Nat.
