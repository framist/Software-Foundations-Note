---
title: Rel
date: 2023-04-16T16:14:50Z
lastmod: 2023-04-16T16:17:28Z
---

# Rel

# 关系的性质    (Rel)

* [关系](https://coq-zh.github.io/SF-zh/lf-current/Rel.html#lab302)
* [基本性质](https://coq-zh.github.io/SF-zh/lf-current/Rel.html#lab303)
* [自反传递闭包](https://coq-zh.github.io/SF-zh/lf-current/Rel.html#lab320)

## 关系

集合 **X** 上的二元*'关系（Relation）'*指所有由两个 **X** 中的元素参数化的命题， 即，有关一对 **X** 中的元素的命题。

```coq
Definition relation (X: Type) := X -> X -> Prop.
```

令人困惑的是，*“关系”原本是个更为通用的词语，然而 Coq 标准库中的“关系” 却单指这一种“某个集合中的元素之间二元关系”*。为了与标准库保持一致， 我们将会沿用这一定义。然而“关系”一词除了指这一意义以外， 也可以指代任何数量的，可能是不同集合之间的更一般的关系。 在讨论中使用“关系”一词时，应该在上下文中解释具体所指的含义。

一个关系的例子是 **nat** 上的 **le**，即“小于或等于”关系，我们通常写作 **n**​~1~ **≤** **n**​~2~。

```coq
Print le.
(* ====> Inductive le (n : nat) : nat -> Prop :=
             le_n : n <= n
           | le_S : forall m : nat, n <= m -> n <= S m *)
Check le : nat -> nat -> Prop.
Check le : relation nat.
```

（为什么我们不直接写成 **Inductive** **le** **:** **relation** **nat**... 呢？ 这是因为我们想要将第一个 **nat** 放在 **:** 的左侧，这能让 Coq 为 **≤** 更为友好的的归纳法则。）

‍

## 基本性质

学过本科离散数学课的人都知道，与关系相关的东西有很多， 包括对关系的性质（如自反性、传递性等），关于某类关系的一般定理， 如何从一种关系构造出另一种关系等等。例如：

### 偏函数 partial

*跟编程领域中一般所说的偏函数（用来固定部分参数）定义不同*

对于集合 **X** 上的关系 **R** ，如果对于任何 **x** 最多只有一个 **y** 使得 **R** **x** **y** 成立 -- 即，**R** **x** **y**​~1~ 和 **R** **x** **y**​~2~ 同时成立蕴含 **y**​~1~ **=** **y**​~2~， 则称 **R** 为*'偏函数'*。

```coq
Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.
```

例如，之前定义的 **next_nat** 关系就是个偏函数。

```coq
Print next_nat.
(* ====> Inductive next_nat (n : nat) : nat -> Prop :=
           nn : next_nat n (S n) *)
Check next_nat : relation nat.

Theorem next_nat_partial_function :
   partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1. inversion H2.
  reflexivity.  Qed.
```

然而，数值上的 **≤** 关系并不是个偏函数。（利用反证法，假设 **≤** 是一个偏函数。然而根据其定义我们有 **0** **≤** **0** 和 **0** **≤** **1**，这样会推出 **0** **=** **1**。这是不可能的，所以原假设不成立。）

```coq
Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense. {
    apply Hc with (x := 0).
    - apply le_n.
    - apply le_S. apply le_n. }
  discriminate Nonsense.   Qed.
```

‍

​#剩余习题未完成#​

‍

### 自反关系 reflexive

集合 **X** 上的*'自反关系'*是指 **X** 的每个元素都与其自身相关。

```coq
Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive. intros n. apply le_n.  Qed.
```

### 传递关系

如果 **R** **a** **b** 和 **R** **b** **c** 成立时 **R** **a** **c** 也成立，则称 **R** 为*'传递关系'*。

```coq
Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).
```

​#剩余习题未完成#​

‍

对称关系与反对称关系

如果 **R** **a** **b** 蕴含 **R** **b** **a**，那么 **R** 就是*'对称关系'*。

```coq
Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).
```

如果 **R** **a** **b** 和 **R** **b** **a** 成立时有 **a** **=** **b**，那么 **R** 就是*'反对称关系'*。

```coq
Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).
```

​#剩余习题未完成#​

### 等价关系

如果一个关系满足自反性、对称性和传递性，那么它就是*'等价关系'*。

```coq
Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).
```

### 偏序关系与预序关系

如果某个关系满足自反性、*'反'*对称性和传递性，那么它就一个是*'偏序关系'*。 在 Coq 标准库中，它被简短地称作“order”。

```coq
Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).
```

预序和偏序差不多，不过它无需满足反对称性。

```coq
Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).
```

```coq
Theorem le_order :
  order le.
Proof.
  unfold order. split.
    - (* refl *) apply le_reflexive.
    - split.
      + (* antisym *) apply le_antisymmetric.
      + (* transitive. *) apply le_trans.  Qed.
```

‍

## 自反传递闭包

关系 **R** 的*'自反传递闭包'*是最小的包含 **R** 的自反传递关系。 在 Coq 标准库的 Relations 模块中，此概念定义如下：

```coq
Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
    | rt_step x y (H : R x y) : clos_refl_trans R x y
    | rt_refl x : clos_refl_trans R x x
    | rt_trans x y z
          (Hxy : clos_refl_trans R x y)
          (Hyz : clos_refl_trans R y z) :
          clos_refl_trans R x z.
```

例如，**next_nat** 关系的自反传递闭包实际上就是 **le**。

```coq
Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split.
  - (* -> *)
    intro H. induction H.
    + (* le_n *) apply rt_refl.
    + (* le_S *)
      apply rt_trans with m. apply IHle. apply rt_step.
      apply nn.
  - (* <- *)
    intro H. induction H.
    + (* rt_step *) inversion H. apply le_S. apply le_n.
    + (* rt_refl *) apply le_n.
    + (* rt_trans *)
      apply le_trans with y.
      apply IHclos_refl_trans1.
      apply IHclos_refl_trans2. Qed.
```

以上对自反传递闭包的定义十分自然：它直接将自反传递闭包定义为“包含 **R** 的，同时满足自反性和传递性的最小的关系”。 然而此定义对于证明来说不是很方便，因为 **rt_trans** 的“非确定性” 有时会让归纳变得很棘手。下面是最常用的定义：

```coq
Inductive clos_refl_trans_1n {A : Type}
                             (R : relation A) (x : A)
                             : A -> Prop :=
  | rt1n_refl : clos_refl_trans_1n R x x
  | rt1n_trans (y z : A)
      (Hxy : R x y) (Hrest : clos_refl_trans_1n R y z) :
      clos_refl_trans_1n R x z.
```

这一新的定义将 **rt_step** 和 **rt_trans** 合并成一条。在此规则的假设中 **R** 只用了一次，这会让归纳法则更简单。

​#剩余习题未完成#​

‍

‍
