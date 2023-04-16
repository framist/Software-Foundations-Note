---
title: Induction
date: 2023-04-16T16:04:09Z
lastmod: 2023-04-16T16:11:16Z
---

# Induction

# 归纳证明    (Induction)

* [归纳法证明](https://coq-zh.github.io/SF-zh/lf-current/Induction.html#lab49)
* [证明里的证明](https://coq-zh.github.io/SF-zh/lf-current/Induction.html#lab54)
* [形式化证明 vs. 非形式化证明](https://coq-zh.github.io/SF-zh/lf-current/Induction.html#lab55)
* [更多练习](https://coq-zh.github.io/SF-zh/lf-current/Induction.html#lab58)

配置环境：

安装 coq 参考：

```coq
# ubuntu
sudo snap install coq-prover
# arch
sudo pacman -S coq  
```

对于我使用的 VSCode +  VScoq 插件环境，推荐使用命令行方式配置 make

```bash
coq_makefile -f _CoqProject *.v -o Makefile
make Basics.vo # 编译
make BasicsTest.vo # 批改作业
```

如果遇到版本错误的问题，重新运行运行一些这些命令即可。

​#TODO#​ 对于 VScoq 插件，得需是当前工作区目录才能正常运行，现在还不知道问题所在。（跟coq的`Export`​对于文件路径的特性有关）

此环境在我的 [GitHub 仓库](https://github.com/framist/Software-Foundations-Note) 中。

‍

其他关于 Coq 的一些用法： #GPT#​

coqtop 是一个信息处理程序，它允许用户执行像打开文件，检查定义，通过命令交互式地编写代码等功能的 Coq 命令。

在编译 Coq 文件时，首先要使用 coqc 命令将 .v 文件编译成 .vo 文件，然后可以使用 coqtop 作为交互式编译器或链接器来使用这些 .vo 文件进行编译。

‍

## 归纳法证明

回想一下 *'自然数的归纳法则'*，你也许曾在高中的数学课上，在某门离散数学课上或 在其它类似的课上学到过它：若 **P**(**n**) 为关于自然数的命题，而当我们想要证明 **P** 对于所有自然数 **n** 都成立时，可以这样推理：* 证明 **P**(**O**) 成立；

* 证明对于任何 **n'**，若 **P**(**n'**) 成立，那么 **P**(**S** **n'**) 也成立。
* 最后得出 **P**(**n**) 对于所有 **n** 都成立的结论。

在 Coq 中的步骤也一样：我们以证明 **P**(**n**) 对于所有 **n** 都成立的目标开始， 然后（通过应用 ==**induction**== 策略）把它分为两个子目标：一个是我们必须证明 **P**(**O**) 成立，另一个是我们必须证明 **P**(**n'**) **→** **P**(**S** **n'**)。下面就是对该定理的用法：

```coq
Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity.  Qed.
```

和 **destruct** 一样，**induction** 策略也能通过 **as**... 从句为引入到 子目标中的变量指定名字。由于这次有两个子目标，因此 **as**... 有两部分，用 **|** 隔开。

在第一个子目标中 **n** 被 **0** 所取代。由于没有新的变量会被引入，因此 **as** **...** 字句的第一部分为空

在第二个子目标中，**n** 被 **S** **n'** 所取代，而对 **n'** 的归纳假设（Inductive Hypothesis），即 **n'** **+** **0** **=** **n'** 则以 **IHn'** 为名被添加到了上下文中。 这两个名字在 **as**... 从句的第二部分中指定。在此上下文中，待证目标变成了 **(**S **n'**) **+** o**0** **=** **S** **n'**；它可被化简为 **S** **(**n' **+** **0)** **=** **S** **n'**，而此结论可通过 **IHn'** 得出。

（其实在这些证明中我们并不需要 **intros**：当 **induction** 策略被应用到包含量化变量的目标中时，它会自动将需要的变量移到上下文中。）

接下来就可以证明喜闻乐见的加法交换律和结合律了。

*这样子的证明会让我有一种瞎试就试出来的感觉，比用传统的方式更不明晰。但证明很快，可以保证他就是对的。后文：*​*((20221127191842-9d5h9nc '形式化证明 vs. 非形式化证明'))*

‍

我们的 **evenb** **n** 定义对 **n** **-** **2** 的递归调用不大方便。这让证明 **evenb** **n** 时更难对 **n** 进行归纳，因此我们需要一个关于 **n** **-** **2** 的归纳假设。 以下引理赋予了 **evenb** **(**S **n**) 另一个特征，使其在归纳时能够更好地工作：#TODO#​ 后文？

‍

## 证明里的证明

*嵌套证明*

简单地陈述并立即证明所需的“子定理”就会很方便。 我们可以用 **assert** 策略来做到。

```coq
Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.  Qed.
```

（当然也可以用 **as** 来命名该断言，与之前的 **destruct** 和 **induction** 一样。例如 **assert** **(0** **+** **n** **=** **n**) **as** **H**。）**assert** 生成的第一个子目标是我们必须证明的已断言的事实， 而在第二个子目标中，我们可以使用已断言的事实在一开始尝试证明的事情上取得进展。

```coq
(* 举例来说，假如我们要证明 (n + m) + (p + q) = (m + n) + (p + q)。 = 两边唯一不同的就是内层第一个子式中 + 的参数 m 和 n 交换了位置， 我们似乎可以用加法交换律（plus_comm）来改写它。然而， rewrite 策略并不知道应该作用在 '哪里'。本命题中 + 用了三次 ， 结果 rewrite → plus_comm 只对 '最外层' 起了作用... *)

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* 我们只需要将 (m + n) 交换为 (n + m)... 看起来 plus_comm 能搞定！*)
  rewrite -> plus_comm.
  (* 搞不定... Coq 选错了要改写的加法！ *)
Abort.

(** 为了在需要的地方使用 [plus_comm]，我们可以（为此这里讨论的 [m] 和 [n]）
    引入一个局部引理来陈述 [n + m = m + n]，之后用 [plus_comm] 证明它，
    并用它来进行期望的改写。 *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity.  Qed.
```

‍

## 形式化证明 vs. 非形式化证明

“*'非形式化证明是算法，形式化证明是代码。'*”

证明是一种交流行为

形式化证明在很多方面都非常有用， 不过它们对人类之间的思想交流而言 *'并不'* 十分高效。特别是 Coq 证明中任何一处的“证明状态”都是完全 隐含的，而非形式化证明则经常反复告诉读者目前证明进行的状态。

‍

‍

## 更多练习

```coq
(** **** 练习：3 星, standard, optional (more_exercises) 

    找一张纸。对于以下定理，首先请 _'思考'_ 
    (a) 它能否能只用化简和改写来证明，
    (b) 它还需要分类讨论（[destruct]），以及 
    (c) 它还需要归纳证明。
    先写下你的预判，然后填写下面的证明（你的纸不用交上来，这只是鼓励你先思考再行动！） *)

...

Theorem zero_nbeq_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  (* 请在此处解答 *)
  (* 只用化简和改写来证明 *)
  simpl. (* TODO: 这里 出现了奇怪的蕴含式 nat -> false = false 是否意味这什么？ *)
  intros H.
  reflexivity.
Qed. 

...

Theorem S_nbeq_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  (* 请在此处解答 *)
  (* 只用化简和改写来证明 *)
  (* TODO: 为何不先证明 =? 的交换率？ *)
  simpl. reflexivity. Qed.

...


(* 可以证明一下排中律, 但不是说直觉主义逻辑不接受排中律？ 是因为 a: bool 而非命题？
*)
Theorem 排中律 : forall a: bool,
    a || (negb a) = true.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
Qed.

(* 乘法分配率 *)
Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
(* 乘法结合率 *)
Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p

(* TODO: 接下来不断用交换律可证明，就是不断代换，能证，不过实在有点麻烦 *)
```

​#TODO#​*这里 出现了奇怪的蕴含式 ​*​*`nat -> false = false`*​*​ 是否意味这什么？其他见上面的代码块。*

**replace** 策略允许你指定一个具体的要改写的子项和你想要将它改写成的项： **replace** **(**t**)** **with** **(**u**)** 会将目标中表达式 **t**（的所有副本）替换为表达式 **u**， 并生成 **t** **=** **u** 作为附加的子目标。在简单的 **rewrite** 作用在目标错误的部分上时 这种做法通常很有用。

​#剩余习题未完成#​

‍
