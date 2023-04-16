---
title: IndProp
date: 2023-04-16T16:12:10Z
lastmod: 2023-04-16T16:12:30Z
---

# IndProp

# 归纳定义的命题    (IndProp)

* [归纳定义的命题](https://coq-zh.github.io/SF-zh/lf-current/IndProp.html#lab206)

  * [偶数性的归纳定义](https://coq-zh.github.io/SF-zh/lf-current/IndProp.html#lab207)
* [在证明中使用证据](https://coq-zh.github.io/SF-zh/lf-current/IndProp.html#lab209)

  * [对证据进行反演](https://coq-zh.github.io/SF-zh/lf-current/IndProp.html#lab210)
  * [对证据进行归纳](https://coq-zh.github.io/SF-zh/lf-current/IndProp.html#lab213)
* [归纳关系](https://coq-zh.github.io/SF-zh/lf-current/IndProp.html#lab218)
* [案例学习：正则表达式](https://coq-zh.github.io/SF-zh/lf-current/IndProp.html#lab227)

  * [remember 策略](https://coq-zh.github.io/SF-zh/lf-current/IndProp.html#lab231)
* [案例学习：改进互映](https://coq-zh.github.io/SF-zh/lf-current/IndProp.html#lab235)
* [额外练习](https://coq-zh.github.io/SF-zh/lf-current/IndProp.html#lab238)

  * [扩展练习：经验证的正则表达式匹配器](https://coq-zh.github.io/SF-zh/lf-current/IndProp.html#lab246)

‍

如何解决 `Require Coq.omega.Omega. ​`​出现的问题：

```bash
COQC IndProp.v
File "./IndProp.v", line 5, characters 0-24:
Error: Cannot find a physical path bound to logical path Coq.omega.Omega.
```

确保 Omega 模块的路径正确配置，并且已经编译。  
您可以在终端中运行以下命令来检查 Omega 模块是否存在：`coqc -where`​。该命令将显示 Coq 安装的路径，其中应包括 Omega 模块的路径。

```bash
$ ls /snap/coq-prover/31/coq-platform/lib/coq/theories/omega/
OmegaLemmas.v  OmegaLemmas.vo  OmegaLemmas.vos  PreOmega.v  PreOmega.vo  PreOmega.vos
```

‍

‍

‍

## 归纳定义的命题

在 [Logic](https://coq-zh.github.io/SF-zh/lf-current/Logic.html) 一章中，我们学习了多种方式来书写命题，包括合取、析取和存在量词。 在本章中，我们引入另一种新的方式：*'归纳定义（Inductive Definitions）'*。

*'注意'*：为简单起见，本章中的大部分内容都用一个归纳定义的“偶数性”作为展示的例子。 你可能会为此感到不解，因为我们已经有一种将偶数性定义为命题的完美方法了（若 **n** 等于某个整数的二倍，那么它是是偶数）。尚若如此，那么请放心， 在本章末尾和以后的章节中，我们会看到更多引人入胜的归纳定义的命题示例。

在前面的章节中，我们已经见过两种表述 **n** 为偶数的方式了：

(1) **evenb** **n** **=** **true**，以及

(2) **∃** **k**, **n** **=** **double** **k**。

然而还有一种方式是通过如下规则来建立 **n** 的偶数性质：

* 规则 **ev_0**: **0** 是偶数。
* 规则 **ev_SS**: 如果 **n** 是偶数, 那么 **S** **(**S **n**) 也是偶数。

为了理解这个新的偶数性质定义如何工作，我们可想象如何证明 **4** 是偶数。 根据规则 **ev_SS**，需要证明 **2** 是偶数。这时，只要证明 **0** 是偶数， 我们可继续通过规则 **ev_SS** 确保它成立。而使用规则 **ev_0** 可直接证明 **0** 是偶数。

接下来的课程中，我们会看到很多类似方式定义的命题。 在非形式化的讨论中，使用简单的记法有助于阅读和书写。 *'推断规则（Inference Rules）'*就是其中的一种。 （我们为此性质取名为 **ev**，因为 **even** 已经用过了。）

$$
\begin{gathered}
\frac{}{\operatorname{ev} ~ \theta} ~~~~(ev_0)
\\
\frac{\operatorname{ev} n}{\operatorname{ev}(S(S n))}
~~~~\left(e_{-} S S\right)
\end{gathered}
$$

若将上面的规则重新排版成推断规则，我们可以这样阅读它，如果线上方的 *'前提（Premises）'*成立，那么线下方的*'结论（Conclusion）'*成立。 比如，规则 **ev_SS** 读做如果 **n** 满足 **even**，那么 **S** **(**S **n**) 也满足。 如果一条规则在线上方没有前提，则结论直接成立。

我们可以通过组合推断规则来展示证明。下面展示如何转译 **4** 是偶数的证明：

```bash
                 --------  (ev_0)
                  ev 0
                 -------- (ev_SS)
                  ev 2
                 -------- (ev_SS)
                  ev 4
```

（为什么我们把这样的证明称之为“树”而非其他，比如“栈”？ 因为一般来说推断规则可以有多个前提。我们很快就会看到一些例子。

‍

### 偶数性的归纳定义

基于上述，可将偶数性质的定义翻译为在 Coq 中使用 **Inductive** 声明的定义， 声明中每一个构造子对应一个推断规则：

```coq
Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS (n : nat) (H : ev n) : ev (S (S n)).
```

‍

这个定义与之前 **Inductive** 定义的用法有一个有趣的区别：一方面， 我们定义的并不是一个 **Type**（如 **nat**），而是一个将 **nat** 映射到 **Prop** 的函数——即关于数的性质。然而真正要关注的是，由于 **ev** 中的 **nat** 参数出现在冒号*'右侧'*，这允许在不同的构造子类型中使用不同的值：例如 **ev_0** 类型中的 **0** 以及 **ev_SS** 类型中的 **S** **(**S **n**)。与此相应， 每个构造子的类型必须在冒号后显式指定，并且对于某个自然数 **n** 来说，每个构造子的类型都必须有 **ev** **n** 的形式。

相反，回忆 **list** 的定义：

```coq
    Inductive list (X:Type) : Type :=
      | nil
      | cons (x : X) (l : list X).
```

它以*'全局的方式'*在冒号*'左侧'*引入了参数 **X**， 强迫 **nil** 和 **cons** 的结果为同一个类型（**list** **X**）。 如果在定义 **ev** 时将 **nat** 置于冒号左侧，就会得到如下错误：

```coq
Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS (H: wrong_ev n) : wrong_ev (S (S n)).
(* ===> Error: Last occurrence of "[wrong_ev]" must have "[n]"
        as 1st argument in "[wrong_ev 0]". *)
```

在 **Inductive** 定义中，类型构造子冒号左侧的参数叫做==形参（Parameter）==， 而右侧的叫做==索引（Index）或注解（Annotation）==。

例如，在 **Inductive** **list** **(**X **:** **Type**) **:=** **...** 中，**X** 是一个形参；而在 **Inductive** **ev** **:** **nat** **→** **Prop** **:=** **...** 中，未命名的 **nat** 参数是一个索引。

在 Coq 中，我们可以认为 **ev** 定义了一个性质 **ev** **:** **nat** **→** **Prop**，其包括 “证据构造子” `ev_0 : ev 0`​ 和 `ev_SS : forall n, ev n -> ev (S (S n))`​。

这些 “证据构造子” 等同于已经证明过的定理。 具体来说，我们可以使用 Coq 中的 **apply** 策略和规则名称来证明某个数的 **ev** 性质……

```coq
Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** ……或使用函数应用的语法： *)

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

(** 我们同样可以对前提中使用到 [ev] 的定理进行证明。 *)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(** 更一般地，我们可以证明以任意数乘 2 是偶数： *)

(** **** 练习：1 星, standard (ev_double)  *)
Theorem ev_double : forall n,
  ev (double n).
Proof.
  (* 请在此处解答 *)
  intros n. rewrite double_plus. induction n.
  - simpl.  apply ev_0.
  - simpl. rewrite <- plus_n_Sm. apply ev_SS. apply IHn.
Qed.
```

## 在证明中使用证据

除了*'构造'*证据（evidence）来表示某个数是偶数，我们还可以*'解构'*这样的证据， 这等于对它的构造进行论证。

对 **ev** 而言，使用 **Inductive** 声明来引入 **ev** 会告诉 Coq， **ev_0** 和 **ev_SS** 构造子不仅是构造偶数证明证据的有效方式， 还是构造一个数满足 **ev** 的证据的*'唯一'*方式。

换句话说，如果某人展示了对于 **ev** **n** 的证据 **E**，那么我们知道 **E** 必是二者其一：

* **E** 是 **ev_0**（且 **n** 为 **O**），或
* **E** 是 **ev_SS** **n'** **E'**（且 **n** 为 **S** **(**S **n'**)，**E'** 为 **ev** **n'** 的证据）.

这样的形式暗示着，我们可以像分析归纳定义的数据结构一样分析形如 **ev** **n** 的假设；特别地，对于这类证据使用*'归纳（induction）'*和*'分类讨论（case analysis）'*来进行论证也是可行的。让我们通过一些例子来学习实践中如何使用他们。

### 对证据进行反演

假设我们正在证明涉及数字 `n`​ 的事实，并且给出了 `ev n`​ 作为假设。我们已经知道如何使用 `destruct`​ 或 `induction`​ 来对 `n`​ 进行情况分析，为`n = O`​的情况和一些`n'`​的情况 `n = S n'`​ 生成单独的子目标。但是，对于某些证明，我们可能会_*直接*_考虑 `ev n`​ 的证据。作为一种工具，我们可以使用 `destruct`​ 来证明 `ev n`​ 的特征。

```coq
Theorem ev_inversion :
  forall (n : nat), ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E.
  destruct E as [ | n' E'].
  - (* E = ev_0 : ev 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.
```

用 **destruct** 解构证据即可证明下述定理：

```coq
Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.
Qed.
```

但是，这种变化不能仅仅通过 **destruct ​**来处理。

```coq
Theorem evSS_ev : forall n,
  ev (S (S n)) -> even n.
```

直观来说，我们知道支撑前提的证据不会由 **ev_0** 组成，因为 **0** 和 **S** 是 **nat** 类型不同的构造子；由此 **ev_SS** 是唯一需要应对的情况（译注：**ev_0** 无条件成立）。 不幸的是，**destruct** 并没有如此智能，它仍然为我们生成两个子目标。 更坏的是，于此同时最终目标没有改变，也无法为完成证明提供任何有用的信息。

```coq
Proof.
  intros n E.
  destruct E as [| n' E'] eqn:EE.
  - (* E = ev_0. *)
    (* 我们须证明 [n] 是偶数，但没有任何有用的假设信息可以使用！ *)
Abort.
```

究竟发生了什么？应用 **destruct** 把性质的参数替换为对应于构造子的值。 这对于证明 **ev_minus2'** 是有帮助的，因为在最终目标中直接使用到了参数 **n**。 然而，这对于 **evSS_ev** 并没有帮助，因为被替换掉的 **S** **(**S **n**) 并没有在其他地方被使用。

如果我们 [remember] 这个术语 [S (S n)]，证明就会通过。 (<u>我们将在下面更详细地讨论 [remember] ​</u>）

```coq
Theorem evSS_ev_remember : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n H. remember (S (S n)) as k. destruct H as [|n' E'].
  - (* E = ev_0 *)
    (* Now we do have an assumption, in which [k = S (S n)] has been
       rewritten as [0 = S (S n)] by [destruct]. That assumption
       gives us a contradiction. 
       现在我们确实有一个假设，其中 [k = S (sn)] 已经
       被 [destruct] 改写为 [0 = S (sn)]。那个假设给我们一个矛盾。
       *)
    discriminate Heqk.
  - (* E = ev_S n' E' *)
    (* This time [k = S (S n)] has been rewritten as [S (S n') = S (S n)]. *)
    injection Heqk as Heq. rewrite Heq in E'. apply E'.
Qed.
```

或者，使用我们的反演引理，证明是直截了当的。

​#TODO#​ `inversion`​ 此章未完成阅读

​#剩余习题未完成#​

‍

### 对证据进行归纳

‍

## 归纳关系

## 案例学习：正则表达式

### remember 策略

## 案例学习：改进互映

## 额外练习

### 扩展练习：经验证的正则表达式匹配器

‍
