From mathcomp Require Import ssreflect ssrbool ssrnat seq.
Require Recdef.

Require Import neko.ordering.

Module Type S.
  Parameters (T: Type) (leT: rel T).
  Axiom leT_total_preorder: TotalPreOrder leT.
End S.

Module LeftistHeap(Import O: S).
  Create HintDb leftist.
  Ltac leftist_simpl :=
    simpl;
    do ![
         autounfold with leftist;
         autorewrite with leftist using simpl
       ].

  Ltac korenani :=
    do ![
         idtac;
         match goal with
         | [ H: forall t1 t2, (?v1, ?v2) = (t1, t2) -> _ |- _ ] => move: H => /(_ v1 v2 eq_refl) H
         end
       ].

  Inductive tree :=
  | Leaf
  | Node of tree & T & tree & nat.

  Definition nil := Leaf.
  Definition singleton x := Node Leaf x Leaf 1.

  Hint Unfold nil singleton : leftist.

  Definition rank t := if t is Node _ _ _ k then k else 0.

  Definition is_empty t := if t is Leaf then true else false.
  Fixpoint size t := if t is Node l _ r _ then (size l + size r).+1 else 0.

  Inductive empty: tree -> Prop := empty_nil: empty Leaf.
  Lemma emptyP t: reflect (empty t) (is_empty t).
  Proof. by apply: (iffP idP); case t => // ? ? ? ? []. Qed.

  Function pair_merge ts {measure (fun (ts: tree*tree) => let (t1, t2) := ts in size t1 + size t2) ts} :=
    match ts with
    | (Leaf, t) | (t, Leaf) => t
    | (Node l1 x1 r1 _ as t1, Node l2 x2 r2 _ as t2) =>
      if leT x1 x2
      then
        let t1' := pair_merge (r1, t2) in
        let t2' := l1 in
        let k1' := rank t1' in
        let k2' := rank t2' in
        if k1' <= k2' then Node t1' x1 t2' k1'.+1 else Node t2' x1 t1' k2'.+1
      else
        let t1' := pair_merge (t1, r2) in
        let t2' := l2 in
        let k1' := rank t1' in
        let k2' := rank t2' in
        if k1' <= k2' then Node t1' x2 t2' k1'.+1 else Node t2' x2 t1' k2'.+1
    end.
  Proof.
    all: by move => * /=; apply/ltP; rewrite (ltn_add2r, ltn_add2l) ltnS leq_addl.
  Qed.

  Definition merge t1 t2 := pair_merge (t1, t2).

  Lemma merge_equation t1 t2:
    merge t1 t2 = match t1 with
                  | Leaf => t2
                  | Node l1 x1 r1 _ =>
                    match t2 with
                    | Leaf => t1
                    | Node l2 x2 r2 _ =>
                      if leT x1 x2
                      then
                        if rank (merge r1 t2) <= rank l1
                        then Node (merge r1 t2) x1 l1 (succn (rank (merge r1 t2)))
                        else Node l1 x1 (merge r1 t2) (succn (rank l1))
                      else
                        if rank (merge t1 r2) <= rank l2
                        then Node (merge t1 r2) x2 l2 (succn (rank (merge t1 r2)))
                        else Node l2 x2 (merge t1 r2) (succn (rank l2))
                    end
                  end.
  Proof. by rewrite /merge pair_merge_equation. Qed.

  Hint Rewrite
       (fun t2 => merge_equation Leaf t2)
       (fun t1 => merge_equation t1 Leaf)
       (fun l1 x1 r1 k1 l2 x2 r2 k2 => merge_equation (Node l1 x1 r1 k1) (Node l2 x2 r2 k2))
    : leftist.

  Definition insert x t := merge (singleton x) t.

  Hint Unfold insert : leftist.

  Fact merge_size t1 t2: size (merge t1 t2) = size t1 + size t2.
  Proof.
    elim: t1 t2 => [|l1 IHl1 x1 r1 IHr1 k1]; elim => [|l2 IHl2 x2 r2 IHr2 k2]; leftist_simpl => //.
    case: ifP => ?; case: ifP => ? /=; rewrite ?IHl1 ?IHr1 ?IHl2 ?IHr2 /=; ring.
  Qed.

  Fact insert_size x t: size (insert x t) = (size t).+1.
  Proof. by rewrite merge_size /=; ring. Qed.

  Fixpoint is_heap t :=
    match t with
    | Leaf => true
    | Node l x r _ =>
      let subheap t' := if t' is Node _ x' _ _ then leT x x' && is_heap t' else true in
      subheap l && subheap r
    end.

  Inductive lowerbound: T -> tree -> Prop :=
  | lowerbound_leaf lb: lowerbound lb Leaf
  | lowerbound_node lb l x r k: leT lb x -> lowerbound x l -> lowerbound x r -> lowerbound lb (Node l x r k).

  Inductive heapified: tree -> Prop :=
  | heapified_leaf: heapified Leaf
  | heapified_node l x r k:  lowerbound x l -> lowerbound x r -> heapified (Node l x r k).

  Hint Constructors lowerbound heapified : leftist.

  Lemma heapifiedP t: reflect (heapified t) (is_heap t).
  Proof.
    apply: (iffP idP).
    - elim: t => [|l IHl x r IHr k].
      + by constructor.
      + case El: l => [|l1 x1 r1 k1]; case Er: r => [|l2 x2 r2 k2]; subst => /=.
        * do !constructor.
        * move => /andP[O2 H2].
          {
            case El2: l2; case Er2: r2; subst => //=.
            all: match type of IHr with (_ -> ?P) => have Hr: P by apply: IHr end; inversion Hr.
            all: do !constructor => //.
          }
        * move => /andP[/andP[O1 H1]].
          {
            case El1: l1; case Er1: r1; subst => //=.
            all: match type of IHl with (_ -> ?P) => have Hl: P by apply: IHl end; inversion Hl.
            all: do !constructor => //.
          }
        * move => /andP[/andP[O1 H1] /andP[O2 H2]].
          {
            case El1: l1; case Er1: r1; case El2: l2; case Er2: r2; subst => //=.
            all: match type of IHl with (_ -> ?P) => have Hl: P by apply: IHl end; inversion Hl.
            all: match type of IHr with (_ -> ?P) => have Hr: P by apply: IHr end; inversion Hr.
            all: do !constructor => //.
          }
    - elim: t => // [t1 IHt1 x t2 IHt2 k].
      move => H; inversion H as [|? ? ? ? Hl Hr] => {H}; subst.
      case Et1: t1 => [|t1l t1x t1r t1k]; case Et2: t2 => [|t2l t2x t2r t2k] //.
      + inversion Hr as [|rlb rl rx rr rk Hr0 Hr1 Hr2 Hr3 Hr4]; first by subst.
        subst; case: Hr4 => *; subst.
        have: is_heap (Node t2l t2x t2r t2k) by apply: IHt2; constructor.
        by simpl; move/andP => [-> ->]; rewrite !andbT.
      + inversion Hl as [|llb ll lx lr lk Hl0 Hl1 Hl2 Hl3 Hl4]; first by subst.
        subst; case: Hl4 => *; subst.
        have: is_heap (Node t1l t1x t1r t1k) by apply: IHt1; constructor.
        by simpl; move/andP => [-> ->]; rewrite !andbT.
      + inversion Hr as [|rlb rl rx rr rk Hr0 Hr1 Hr2 Hr3 Hr4]; first by subst.
        inversion Hl as [|llb ll lx lr lk Hl0 Hl1 Hl2 Hl3 Hl4]; first by subst.
        subst; case: Hr4; case: Hl4 => *; subst.
        have: is_heap (Node t1l t1x t1r t1k) by apply: IHt1; constructor.
        have: is_heap (Node t2l t2x t2r t2k) by apply: IHt2; constructor.
        by simpl; do !move/andP => [-> ->]; rewrite !andbT; apply/andP.
  Qed.

  Fact nil_is_heap: is_heap nil.
  Proof. done. Qed.

  Fact singleton_is_heap x: is_heap (singleton x).
  Proof. done. Qed.

  Inductive Split: Type :=
  | Split_empty
  | Split_min_rest of T & tree.

  Definition split_min t :=
    match t with
    | Leaf => Split_empty
    | Node l x r _ => Split_min_rest x (merge l r)
    end.

  Section Fold.
    Variable A: Type.
    Variable f: T -> A -> A.

    Function fold (a: A) t {measure size t} :=
      match t with
      | Leaf => a
      | Node l x r t' => fold (f x a) (merge l r)
      end.
    Proof. by move => *; rewrite merge_size. Qed.
  End Fold.

  Arguments fold {A}.

  Hint Rewrite (fun A f a => fold_equation A f a Leaf)
       (fun A f a l x r k => fold_equation A f a (Node l x r k))
    : leftist.

  Definition min x0 t := if t is Node _ x _ _ then x else x0.
  Definition drop_min t := if t is Node l _ r _ then merge l r else Leaf.

  Lemma min_correct t x0: ~ empty t -> heapified t  -> lowerbound (min x0 t) t.
  Proof.
    case t => //= l x r k _ H; inversion H; subst.
    constructor => //; exact: reflexivity.
  Qed.

  Fact min_empty t x0: is_empty t -> min x0 t = x0.
  Proof. by move/emptyP; case. Qed.

  Fact min_singleton x x0: min x0 (singleton x) = x.
  Proof. done. Qed.

  Fact lowerboundW {lb lb' t}: leT lb' lb -> lowerbound lb t -> lowerbound lb' t.
  Proof.
    case: t => [|l x r k] L; first by constructor.
    move => H; inversion H; subst; constructor => //.
    exact: (transitivity lb).
  Qed.

  Fact lowerbound_merge x t1 t2: lowerbound x t1 -> lowerbound x t2 -> lowerbound x (merge t1 t2).
  Proof.
    elim: t1 t2 x => [|t1l IHt1l t1x t1r IHt1r t1k] t2; first by leftist_simpl.
    elim: t2 => [|t2l IHt2l t2x t2r IHt2r t2k] x; first by leftist_simpl.
    move => LB1 LB2.
    inversion LB1; subst; leftist_simpl => //.
    inversion LB2; subst; leftist_simpl => //.
    case: ifP => [|/negP] L; case: ifP => R; constructor => //.
    1,2: by apply: IHt1r => //; constructor => //.
    all: by apply: IHt2r => //; constructor => //; have [/orP[]]: leT t2x t1x || leT t1x t2x by exact: totality.
  Qed.

  Hint Resolve lowerbound_merge : leftist.

  Fact merge_preserve_heap t1 t2: is_heap t1 -> is_heap t2 -> is_heap (merge t1 t2).
  Proof.
    move => /heapifiedP H1 /heapifiedP H2; apply/heapifiedP.
    inversion H1 as [|l1 x1 r1 k1 H1l H1r]; subst; first by leftist_simpl.
    inversion H2 as [|l2 x2 r2 k2 H2l H2r]; subst; first by leftist_simpl.
    leftist_simpl.
    case: ifP => [|/negP] L; case: ifP => R; auto with leftist.
    all: have [/orP[] //]: leT x1 x2  || leT x2 x1 by exact: totality.
    all: auto with leftist.
  Qed.

  Definition to_seq t := rev (fold cons [:: ] t).

  Hint Unfold to_seq : leftist.

  Definition from_seq s := seq.foldr insert nil s.
End LeftistHeap.

Module NatOrd <: S.
  Definition T := nat.
  Definition leT := leq.
  Definition leT_total_preorder := ordering.Nat.Leq.
End NatOrd.

Module Import NatLeftistHeap := LeftistHeap NatOrd.

Example test01: to_seq (merge (singleton 1) (singleton 2)) = [:: 1; 2].
Proof. by leftist_simpl; compute. Qed.

Example test02: to_seq (merge (singleton 2) (singleton 1)) = [:: 1; 2].
Proof. by leftist_simpl; compute. Qed.


Function to_seq_naive t {measure size t}: seq nat :=
  match t with
  | Leaf => [:: ]
  | Node l x r _ => [:: x & to_seq_naive (merge l r) ]
  end.
Proof. by move => ? ? ? ? ? ?; subst; rewrite merge_size /=. Qed.

Example test03: to_seq_naive (from_seq [:: 6; 9; 3; 2; 0; 1; 4; 8; 5; 7]) = iota 0 10.
Proof.
Admitted.
