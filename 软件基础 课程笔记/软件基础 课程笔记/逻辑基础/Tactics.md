---
title: Tactics
date: 2023-04-16T16:08:20Z
lastmod: 2023-04-16T16:09:35Z
---

# Tactics

# 更多基本策略    (Tactics)

* [apply 策略](https://coq-zh.github.io/SF-zh/lf-current/Tactics.html#lab138)
* [apply ](https://coq-zh.github.io/SF-zh/lf-current/Tactics.html#lab142)​**[with](https://coq-zh.github.io/SF-zh/lf-current/Tactics.html#lab142)**​[ 策略](https://coq-zh.github.io/SF-zh/lf-current/Tactics.html#lab142)
* [The ](https://coq-zh.github.io/SF-zh/lf-current/Tactics.html#lab144)​**[injection](https://coq-zh.github.io/SF-zh/lf-current/Tactics.html#lab144)**​[ and ](https://coq-zh.github.io/SF-zh/lf-current/Tactics.html#lab144)​**[discriminate](https://coq-zh.github.io/SF-zh/lf-current/Tactics.html#lab144)**​[ Tactics](https://coq-zh.github.io/SF-zh/lf-current/Tactics.html#lab144)
* [对假设使用策略](https://coq-zh.github.io/SF-zh/lf-current/Tactics.html#lab147)
* [变换归纳假设](https://coq-zh.github.io/SF-zh/lf-current/Tactics.html#lab148)
* [展开定义](https://coq-zh.github.io/SF-zh/lf-current/Tactics.html#lab153)
* [对复合表达式使用 ](https://coq-zh.github.io/SF-zh/lf-current/Tactics.html#lab154)​**[destruct](https://coq-zh.github.io/SF-zh/lf-current/Tactics.html#lab154)**
* [复习](https://coq-zh.github.io/SF-zh/lf-current/Tactics.html#lab157)
* [附加练习](https://coq-zh.github.io/SF-zh/lf-current/Tactics.html#lab158)

本章额外介绍了一些证明策略和手段， 它们能用来证明更多关于函数式程序的有趣性质。

我们会看到：如何在“**向前证明**”和“**向后证明**”两种风格中使用辅助引理；

* 如何对数据构造子进行论证，特别是，如何利用它们<u>单射且不交的事实</u>；
* 如何增强归纳假设，以及何时需要增强；
* 还有通过分类讨论进行论证的更多细节。

## apply 策略

我们经常会遇到待证目标与上下文中的前提或已证引理*'刚好相同'*的情况。

我们可以像之前那样用“**rewrite** **→** **eq**​~2~. **reflexivity**.”来完成。 不过如果我们使用 **apply** 策略，只需一步就能完成

**apply** 策略也可以配合*'条件（Conditional）'*假设和引理来使用： 如果被应用的语句是一个蕴含式，那么该<u>蕴含式的前提</u>就会被添加到待证子目标列表中。

```coq
Theorem silly2 : forall (n m o p : nat),
    n = m ->
    (n = m -> [n;o] = [m;p]) ->
    [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.  Qed.
```

​#TODO#​ 有待加深理解

通常，当我们使用 **apply** **H** 时，语句 **H** 会以一个引入了某些 *'通用变量（Universal Variables）'* 的 **∀** 开始。在 Coq 针对 **H** 的结论匹配当前目标时，它会尝试为这些变量查找适当的值。例如， 当我们在以下证明中执行 **apply** **eq**​~2~ 时，**eq**​~2~ 中的通用变量 **q** 会以 **n** 实例化，而 **r** 会以 **m** 实例化。

‍

## apply **with** 策略

...我们必须在 **apply** 的调用后面加上 "**with** **(**m**:=[**c**,**d**])**" 来显式地提供一个实例。

```coq
  apply trans_eq with (m:=[c;d]).
```

（实际上，我们通常不必在 **with** 从句中包含名字 **m**，Coq 一般足够聪明来确定我们实例化的变量。我们也可以写成： **apply** **trans_eq** **with** **[**c**;**d**]**。）

```coq
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  (* 请在此处解答 *)
  intros n m o p eq1 eq2.
  apply trans_eq with (m).
  apply eq2. apply eq1. Qed.
```

‍

## **injection** 和 **discriminate** 策略

回想自然数的定义：

```coq
 Inductive nat : Type :=
   | O
   | S (n : nat).
```

我们可从该定义中观察到，所有的数都是两种形式之一：要么是构造子 **O**， 要么就是将构造子 **S** 应用到另一个数上。不过这里还有无法直接看到的： 自然数的定义中还蕴含了两个事实：

* 构造子 **S** 是*'*​==*单射（Injective）*==​*'*或*'一一对应'*的。 即，如果 **S** **n** **=** **S** **m**，那么 **n** **=** **m** 必定成立。
* 构造子 **O** 和 **S** 是*'*​==*不相交（Disjoint）*==​*'*的。 即，对于任何 **n**，**O** 都不等于 **S** **n**。

类似的原理同样适用于所有归纳定义的类型：所有构造子都是单射的， 而不同构造子构造出的值绝不可能相等。对于列表来说，**cons** 构造子是单射的， 而 **nil** 不同于任何非空列表。对于布尔值来说，**true** 和 **false** 是不同的。 因为 **true** 和 **false** 二者都不接受任何参数，它们既不在这边也不在那边。 其它归纳类型亦是如此。

例如，我们可以使用定义在 **Basics.v** 中的 **pred** 函数来证明 **S** 的单射性。 .

```coq
Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H1. reflexivity.
Qed.
```

这个技巧可以通过编写等价的 **pred** 来推广到任意的构造子上 —— 即编写一个“撤销”一次构造子调用的函数。为此，Coq 提供了更加简便的 **injection** 策略，它能让我们利用任意构造子的单射性。 下面是使用 **injection** 对上面定理的另一种证法：

```coq
Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.

(** 通过在此处编写 [injection H as Hmn]，我们让 Coq
    利用构造子的单射性来产生所有它能从 [H] 所推出的等式（本例中为等式 [n = m]）。
    每一个这样的等式都作为假设（本例中为 [Hmn]）被添加到上下文中。
*)

  injection H as Hnm. apply Hnm.
Qed.
```

以下例子展示了一个 **injection** 如何直接得出多个等式。

```coq
Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  (* m = o -> n = o -> [n] = [m] *)
  injection H as H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.
```

‍

这就是构造器的 injectivity（注射性？）。那 disjointness （不交性？）呢？

不交性的原则认为两个以不同构造器开头的项（比如 [O] 和 [S]，或 [true] 和 [false]）永远不会相等。这意味着，在某个上下文中，如果我们假设这两个项相等，我们就有理由得出任何我们想要的结论，因为这个假设是毫无意义的。

**discriminate** 策略体现了这个原则：它用于处理涉及不同构造器的等式的假设（例如 [S n = O]），它立即解决当前目标。这里有一个例子：

```coq
Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n.

(** 我们可以通过对 [n] 进行分类讨论来继续。第一种分类是平凡的。 *)

  destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    intros H. reflexivity.

(** However, the second one doesn't look so simple: 
    然而，第二个看起来并不那么简单：
    assuming [0 =? (S n') = true], we must show [S n' = 0]!  
    The way forward is to observe that the assumption itself 
    is nonsensical: 
    前进的方法是观察这个假设本身是毫无意义的： *)

  - (* n = S n' *)
    simpl.

(**
    如果我们对这个假设使用 [discriminate] ，
    Coq 便会确认我们当前正在证明的目标不可行，并同时移除它，不再考虑。 *)

    intros H. discriminate H.
Qed.

```

*这种情况之前也出现过，不过是用 rewrite 来奇怪地解决了的*

本例是逻辑学原理==*'爆炸原理'*==的一个实例，它断言矛盾的前提会推出任何东西， 甚至是假命题！

```coq
Theorem discriminate_ex1 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. Qed.
```

> *这也与蕴含式的定义相同：*
>
> |p<br />|q|p->q|
> | :----| :--| :-----|
> |1|0|0|
> |0|1|1|
> |1|1|1|
> |0|0|1|
>
> [爆炸原理](https://zh.wikipedia.org/zh-cn/%E7%88%86%E7%82%B8%E5%8E%9F%E7%90%86)
>
> **爆炸原理**（principle of explosion, "from falsehood, anything (follows)"），是[经典逻辑](https://zh.wikipedia.org/wiki/%E7%BB%8F%E5%85%B8%E9%80%BB%E8%BE%91 "经典逻辑")中陈述从[矛盾](https://zh.wikipedia.org/wiki/%E7%9F%9B%E7%9B%BE "矛盾")中可以得出任何事物的规则。用更加形式化的术语，从形如 *P* ∧ ¬*P* 的[命题](https://zh.wikipedia.org/wiki/%E5%91%BD%E9%A2%98 "命题")可以推导出任何任意的 *Q* (ex contradictione quodlibet (ECQ))^[[1]](https://zh.wikipedia.org/zh-cn/%E7%88%86%E7%82%B8%E5%8E%9F%E7%90%86#cite_note-1)^。 “爆炸”指称接受一个单一的矛盾到一个系统中会导致整体定理的“爆炸”。
>
> $$
> \displaystyle (P\land \lnot P)\rightarrow Q
> $$
>
> ​#TODO#​ 除了矛盾平常的一目了然的不真实性之外，这是对在形式系统中不允许 *P* ∧ ¬*P* 为真的主要逻辑论证: 在其中任何任意的[公式](https://zh.wikipedia.org/wiki/%E5%85%AC%E5%BC%8F "公式")都是[定理](https://zh.wikipedia.org/wiki/%E5%AE%9A%E7%90%86 "定理")的系统是[琐碎的](https://zh.wikipedia.org/wiki/%E7%91%A3%E7%A2%8E%E8%AB%96 "琐碎论")。所以爆炸原理证明了[无矛盾律](https://zh.wikipedia.org/wiki/%E6%97%A0%E7%9F%9B%E7%9B%BE%E5%BE%8B "无矛盾律")的正当性。

爆炸原理可能令你费解，那么请记住上述证明*'并不'*肯定其后件， 而是说明：*'如果'*荒谬的前件成立，*'那么'*就会得出荒谬的结论， 如此一来我们将生活在一个不一致的宇宙中，这里每个陈述都是正确的。<u>​ 下一章将进一步讨论爆炸原理</u>。

**构造子的单射性**能让我们论证 **∀** **(**n **m** **:** **nat**), **S** **n** **=** **S** **m** **→** **n** **=** **m**。 此蕴含式的逆形式是一个构造子和函数的更一般的实例， 在后面我们会发现它用起来很方便：

```coq
Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq.  reflexivity.  Qed.

Theorem eq_implies_succ_equal : forall (n m : nat),
    n = m -> S n = S m.
Proof. intros n m H. apply f_equal. apply H. Qed.
```

还有一个名为 `f_equal`​ 的策略，可以证明这样的定理。给定形如 [f a1 ... an = g b1 ... bn] 的目标，[f_equal] 策略会产生形如 [f = g]、[a1 = b1]、...、[an = bn] 的子目标。同时，[f_equal] 会自动解决任何足够简单（例如可以立即通过 [reflexivity] 证明）的子目标。

```coq
Theorem eq_implies_succ_equal' : forall (n m : nat),
    n = m -> S n = S m.
Proof. intros n m H. f_equal. apply H. Qed.
```

​#TODO#​ *但  f_equal 不是自己定义的 Theorem 吗，为什么可以直接用作策略？*

‍

## 对假设使用策略 apply in

默认情况下，大部分策略会作用于目标公式并保持上下文不变。然而， 大部分策略还有对应的变体来对上下文中的语句执行类似的操作。

‍

类似地，**apply** **L** **in** **H** 会针对上下文中的假设 **H** 匹配某些 （形如 **X** **→** **Y** 中的）条件语句 **L**。然而，与一般的 **apply** 不同 （它将匹配 **Y** 的目标改写为子目标 **X**），**apply** **L** **in** **H** 会针对 **X** 匹配 **H**，如果成功，就将其替换为 **Y**。

换言之，**apply** **L** **in** **H** 给了我们一种“==正向推理==”的方式：根据 **X** **→** **Y** 和一个匹配 **X** 的假设，它会产生一个匹配 **Y** 的假设。作为对比，**apply** **L** 是一种“==反向推理==”：它表示如果我们知道 **X** **→** **Y** 并且试图证明 **Y**， 那么证明 **X** 就足够了。

**正向推理**从*'给定'*的东西开始（即前提、已证明的定理）， 根据它们迭代地刻画结论直到抵达目标。**反向推理**从*'目标'*开始， 迭代地推理蕴含目标的东西，直到抵达前提或已证明的定理。

你在数学或计算机科学课上见过的非形式化证明可能倾向于正向推理。 <u>通常，Coq 习惯上倾向于使用反向推理</u>，但在某些情况下，正向推理更易于思考。

​#TODO#​ 此节有待加深理解

‍

## 变换归纳假设 generalize dependent

在 Coq 中进行归纳证明时，有时控制归纳假设的确切形式是十分重要的。 特别是，在调用 **induction** 策略前，我们有时需要用 **intros** 将假设从目标移到上下文中时要十分小心。例如，假设我们要证明 **double** 函数是单射的 -- 即，它将不同的参数映射到不同的结果：  
       **Theorem** **double_injective**: **∀** **n** **m**,  
         **double** **n** **=** **double** **m** **→** **n** **=** **m**.

此证明的开始方式有点微妙：如果我们以  
       **intros** **n**. **induction** **n**.

开始，那么一切都好（#TODO#​ 为什么？）。然而假如以  
       **intros** **n** **m**. **induction** **n**.

开始，就会卡在归纳情况中...

此时，归纳假设 **IHn'** *'不会'*给出 **n'** **=** **m'** -- 会有个额外的 **S** 阻碍 -- 因此该目标无法证明。

```coq
Theorem double_injective_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m' *) apply f_equal.

(** 此时，归纳假设 [IHn'] _'不会'_给出 [n' = m'] -- 会有个额外的 [S] 阻碍 --
    因此该目标无法证明。 *)

Abort.
```

要理解为什么它很奇怪，我们来考虑一个具体的（任意但确定的）**m** -- 比如说 **5**。该语句就会这样说：如果我们知道

* **Q** = “若 **double** **n** **=** **10** 则 **n** **=** **5**”

那么我们就能证明

* **R** = “若 **double** **(**S **n**) **=** **10** 则 **S** **n** **=** **5**”。

但是知道 **Q** 对于证明 **R** 来说并没有任何帮助！（如果我们试着根据 **Q** 证明 **R**，就会以“假设 **double** **(**S **n**) **=** **10**..”这样的句子开始， 不过之后我们就会卡住：知道 **double** **(**S **n**) 为 **10** 并不能告诉我们 **double** **n** 是否为 **10**。（实际上，它强烈地表示 **double** **n** *'不是'* **10**！） 因此 **Q** 是没有用的。）

​#TODO#​ 有待学习

在 **induction** 之前做一些 **intros** 来获得更一般归纳假设并不总是奏效。 有时需要对量化的变量做一下*'重排'*。例如，假设我们想要通过对 **m** 而非 **n** 进行归纳来证明 **double_injective**。

```coq
Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction m as [| m' IHm'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
        (* 和前面一样，又卡在这儿了。 *)
Abort.
```

问题在于，要对 **m** 进行归纳，我们首先必须对 **n** 归纳。 （而如果我们不引入任何东西就执行 **induction** **m**，Coq 就会自动为我们引入 **n**！）

我们可以对它做什么？一种可能就是改写该引理的陈述使得 **m** 在 **n** 之前量化。 这样是可行的，不过它不够好：我们不想调整该引理的陈述来适应具体的证明策略！ 我们更想以最清晰自然的方式陈述它。

我们可以先引入所有量化的变量，然后*'重新一般化（re-generalize）'* 其中的一个或几个，选择性地从上下文中挑出几个变量并将它们放回证明目标的开始处。 用 ==**generalize**==​==​ ​==​==**dependent**== （泛化依赖？）策略就能做到。

```coq
Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m.
  (* [n] and [m] are both in the context *)
  generalize dependent n.
  (* 现在 [n] 回到了目标中，我们可以对 [m] 进行归纳并得到足够一般的归纳假设了。 *)
  induction m as [| m' IHm'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'. injection eq as goal. apply goal. Qed.
```

我们来看一下此定理的非形式化证明。注意我们保持 **n** 的量化状态并通过归纳证明的命题，对应于我们形式化证明中依赖的一般化。

*'定理'*：对于任何自然数 **n** 和 **m**，若 **double** **n** **=** **double** **m**，则 **n** **=** **m**。

*'证明'*：令 **m** 为一个 **nat**。我们通过对 **m** 进行归纳来证明，对于任何 **n**， 若 **double** **n** **=** **double** **m**，则 **n** **=** **m**。

* 首先，设 **m** **=** **0**，而 **n** 是一个数使得 **double** **n** **=** **double** **m**。 我们必须证明 **n** **=** **0**。  
  由于 **m** **=** **0**，根据 **double** 的定义，我们有 **double** **n** **=** **0**。此时对于 **n** 需要考虑两种情况。若 **n** **=** **0**，则得证，因为 **m** **=** **0** **=** **n**，正如所需。 否则，若对于某个 **n'** 有 **n** **=** **S** **n'**，我们就会导出矛盾：根据 **double** 的定义，我们可得出 **double** **n** **=** **S** **(**S **(**double **n'**))，但它与 **double** **n** **=** **0** 相矛盾。
* 其次，设 **m** **=** **S** **m'**，而 **n** 同样是一个数使得 **double** **n** **=** **double** **m**。 我们必须证明 **n** **=** **S** **m'**，根据归纳假设，对于任何数 **s**，若 **double** **s** **=** **double** **m'**，则 **s** **=** **m'**。  
  根据 **m** **=** **S** **m'** 的事实以及 **double** 的定义我们有 **double** **n** **=** **S** **(**S **(**double **m'**))。 此时对于 **n** 需要考虑两种情况。  
  若 **n** **=** **0**，则根据 **double** **n** **=** **0** 的定义会得出矛盾。  
  故存在 **n'** 使得 **n** **=** **S** **n'**。再次根据 **double** 之定义，可得 **S** **(**S **(**double **n'**)) **=** **S** **(**S **(**double **m'**))。再由构造子单射可知 **double** **n'** **=** **double** **m'**。以**n'** 代入归纳假设，推得 **n'** **=** **m'**，故显然 **S** **n'** **=** **S** **m'**， 其中 **S** **n'** **=** **n**，**S** **m'** **=** **m**，所以原命题得证。 ☐

‍

‍

## 展开定义 unfold

有时候我们需要手动展开一个由 Definition 定义引入的名称，以便我们可以操作它所表示的表达式。例如，

```coq
Definition square n := n * n.
Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.
  unfold square.     (* <== *)
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
    { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.
```

为此，我们可以手动用 ==**unfold**== 展开 **square** 的定义。

我们已经观察到，像 **simpl**、**reflexivity** 和 **apply** 这样的策略， 通常总会在需要时自动展开函数的定义。然而，这种自动展开有些保守。一种更直白的方式就是使用 `unfold`​ 明确地告诉 Coq 去展开

‍

## 对复合表达式使用 **destruct**

我们已经见过许多通过 **destruct** 进行情况分析来处理一些变量的值了。 有时我们需要根据某些*'表达式'*的结果的情况来进行推理。我们也可以用 **destruct** 来做这件事。

在前面的证明中展开 **sillyfun** 后，我们发现卡在 **if** **(**n **=?** **3)** **then** **...** **else** **...** 上了。但由于 **n** 要么等于 **3** 要么不等于，因此我们可以用 **destruct** **(**eqb **n** **3)** 来对这两种情况进行推理。*使用 destruct 拆开 if 分支*

通常，**destruct** 策略可用于对任何计算结果进行情况分析。如果 **e** 是某个表达式，其类型为归纳定义的类型 **T**，那么对于 **T** 的每个构造子 **c**，**destruct** **e** 都会生成一个子目标，其中（即目标和上下文中）所有的 **e** 都会被替换成 **c**。

‍

**destruct** 策略的 **eqn**: 部分是可选的。然而在用 **destruct** 结构复合表达式时，<u>**eqn**</u>​<u>: 记录的信息是十分关键的</u>： 如果我们丢弃它，那么 **destruct** 会擦除我们完成证明时所需的信息。

...

问题在于 destruct 执行的替换非常残酷 - 在这种情况下，它丢弃了每一个 n =? 3 的出现，但我们需要保留一些对这个表达式的记忆，以及它是如何被 destruct 的，因为我们需要能够推理出，由于在案例分析的这个分支中 n =? 3 = true，所以必须有 n = 3，从而得出 n 是奇数。我们在这里想要做的是替换掉所有现有的 n =? 3 的出现，但同时在上下文中添加一个方程式，记录我们所处的情况。这恰恰是 eqn: 限定符所做的。

```coq
Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
  (* 现在我们的状态和前面卡住的地方一样了，除了上下文中包含了额外的相等关系假设，
     它就是我们继续推进所需要的。 *)
    - (* e3 = true *) apply eqb_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    - (* e3 = false *)
     (* 当我们到达正在推理的函数体中第二个相等关系测试时，我们可以再次使用
        [eqn:]，以便结束此证明。 *)
      destruct (n =? 5) eqn:Heqe5.
        + (* e5 = true *)
          apply eqb_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        + (* e5 = false *) discriminate eq.  Qed.
```

‍

## 复习

现在我们已经见过 Coq 中最基础的策略了。未来的章节中我们还会介绍更多， <u>之后我们会看到一些更加强大的</u>​<u>*'自动化'*</u>​<u>策略，它能让 Coq 帮我们处理底层的细节</u>。

下面是我们已经见过的：

* **intros**：将前提/变量从证明目标移到上下文中
* **reflexivity**：（当目标形如 **e** **=** **e** 时）结束证明
* **apply**：用前提、引理或构造子证明目标
* **apply**... **in** **H**：将前提、引理或构造子应用到上下文中的假设上（正向推理）
* **apply**... **with**...：为无法被模式匹配确定的变量显式指定值
* **simpl**：化简目标中的计算
* **simpl** **in** **H**：化简前提中的计算
* **rewrite**：使用相等关系假设（或引理）来改写目标
* **rewrite** **...** **in** **H**：使用相等关系假设（或引理）来改写前提
* **symmetry**：将形如 **t**=**u** 的目标改为 **u**=**t**
* **symmetry** **in** **H**：将形如 **t**=**u** 的前提改为 **u**=**t**
* **unfold**：用目标中的右式替换定义的常量
* **unfold**... **in** **H**：用前提中的右式替换定义的常量
* **destruct**... **as**...：对归纳定义类型的值进行情况分析
* **destruct**... **eqn**:...：为添加到上下文中的等式指定名字， 记录情况分析的结果
* **induction**... **as**...: 对归纳定义类型的值进行归纳
* **injection**: reason by injectivity on equalities between values of inductively defined types （#GPT#​通过在归纳定义类型的值之间的等式上进行注射性推理）
* **discriminate**: reason by disjointness of constructors on equalities between values of inductively defined types （#GPT#​ 通过归纳定义类型的值之间的等式上构造器的不交性进行推理）
* **assert** **(**H**:** **e**)（或 **assert** **(**e**)** **as** **H**）：引入“局部引理”**e** 并称之为 **H**
* **generalize** **dependent** **x**：将变量 **x**（以及任何依赖它的东西） 从上下文中移回目标公式内的前提中

‍

## 附加练习

​#TODO#​ 本章还剩余大量习题未完成

‍

```coq

Definition split_combine_statement : Prop
  (* （“[: Prop]” 表示我们在这里给出了一个逻辑命题。） *)
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.

Theorem split_combine : split_combine_statement.
Proof.
(* 请在此处解答 *) Admitted.
```

‍
