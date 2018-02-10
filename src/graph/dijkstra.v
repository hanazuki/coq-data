From mathcomp Require Import ssreflect ssrbool ssrnat fintype fingraph seq.
Require Recdef.
Require Import neko.heap.leftiest.

Section Dijkstra.
  Parameter V: finType.
  Parameter e: rel V.
  Definition cost := nat.
  Parameter c: V -> V -> cost.

  Definition cnode: Type := V * cost.
  Definition cpath: Type := seq cnode.

  Function dijkstra (s: V): cpath :=
    

End Dijkstra.