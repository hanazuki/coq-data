From mathcomp Require Import ssreflect ssrbool ssrnat eqtype fintype fingraph seq.
Require Recdef.
Require neko.heap.leftist.
Require Import neko.ordering.

Module Dijkstra.
  Parameter V: finType.
  Parameter g: V -> seq V.
  Definition Cost: Type := nat.
  Parameter cost: V -> V -> Cost.

  Definition cnode: Type := V * Cost.
  Definition cpath: Type := seq cnode.

  Module Pair <: leftist.S.
    Definition T: Type := nat * cpath.
    Definition leT (x y: T) :=
      let '(x', _) := x in
      let '(y', _) := y in
      x' <= y'.

    Instance leT_total_preorder: TotalPreOrder leT.
    Proof.
      constructor.
      constructor.
      - case => ? _ /=; exact: leqnn.
      - case => ? ?; case => ? ?; case => ? ? /=; exact: leq_trans.
      - case => ? ?; case => ? ? /=; exact: leq_total.
    Defined.
  End Pair.

  Module Import pqueue := leftist.LeftistHeap Pair.

  Definition lt_pair' (vs_q1 vs_q2: seq V * tree) :=
    let '(vs1, q1) := vs_q1 in
    let '(vs2, q2) := vs_q2 in
    (seq.size vs1 < seq.size vs2) || ((seq.size vs1 == seq.size vs2) && (size q1 < size q2)) = true.

  Function dijkstra' (vs_q: seq V * tree) {wf lt_pair' vs_q}: cpath :=
    let '(vs, q) := vs_q in
    match split_min q with
    | Split_empty => [:: ]
    | Split_min_rest m q' =>
      if m is (_, [:: (v, d) & _ ])
      then
        dijkstra' (vs, q')
      else
        [:: ]
    end.

End Dijkstra.
