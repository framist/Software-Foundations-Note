---
title: Hoare
date: 2023-04-26T16:40:37Z
lastmod: 2023-04-26T17:43:35Z
---

# Hoare

# 霍尔逻辑（第一部分）    (Hoare)

* [断言](https://coq-zh.github.io/SF-zh/plf-current/Hoare.html#lab51)
* [霍尔三元组](https://coq-zh.github.io/SF-zh/plf-current/Hoare.html#lab53)
* [证明规则](https://coq-zh.github.io/SF-zh/plf-current/Hoare.html#lab56)

  * [赋值](https://coq-zh.github.io/SF-zh/plf-current/Hoare.html#lab57)
  * [缩放](https://coq-zh.github.io/SF-zh/plf-current/Hoare.html#lab62)
  * [题外话：eapply 策略](https://coq-zh.github.io/SF-zh/plf-current/Hoare.html#lab63)
  * [跳过](https://coq-zh.github.io/SF-zh/plf-current/Hoare.html#lab65)
  * [顺序](https://coq-zh.github.io/SF-zh/plf-current/Hoare.html#lab66)
  * [条件](https://coq-zh.github.io/SF-zh/plf-current/Hoare.html#lab70)
  * [循环](https://coq-zh.github.io/SF-zh/plf-current/Hoare.html#lab75)
* [总结](https://coq-zh.github.io/SF-zh/plf-current/Hoare.html#lab78)
* [附加练习](https://coq-zh.github.io/SF-zh/plf-current/Hoare.html#lab79)

> **霍尔逻辑**（英语：Hoare Logic），又称**弗洛伊德-霍尔逻辑**（Floyd–Hoare logic），是[英国](https://zh.wikipedia.org/wiki/%E8%8B%B1%E5%9B%BD "英国")​[计算机科学家](https://zh.wikipedia.org/wiki/%E8%AE%A1%E7%AE%97%E6%9C%BA%E7%A7%91%E5%AD%A6%E5%AE%B6 "计算机科学家")​[东尼·霍尔](https://zh.wikipedia.org/wiki/%E6%9D%B1%E5%B0%BC%C2%B7%E9%9C%8D%E7%88%BE "东尼·霍尔")开发的形式系统，这个系统的用途是为了使用严格的[数理逻辑](https://zh.wikipedia.org/wiki/%E6%95%B0%E7%90%86%E9%80%BB%E8%BE%91 "数理逻辑")推理来替[计算机程序](https://zh.wikipedia.org/wiki/%E8%AE%A1%E7%AE%97%E6%9C%BA%E7%A8%8B%E5%BA%8F "计算机程序")的[正确性](https://zh.wikipedia.org/wiki/%E6%AD%A3%E7%A1%AE%E6%80%A7 "正确性")提供一组逻辑规则。

‍

在*'逻辑基础'*（*'软件基础'* 的第一章) 中， 我们用课程前面的部分中学习的数学工具研究了一个小型编程语言 Imp 。

* 我们给 Imp 定义了<u>*'抽象语法树（abstract syntax trees）'*</u>； 还有<u>*'求值关系（evaluation relation）'*</u>​<u>（一个在状态上的偏函数</u>​<u>`==>`</u>​<u>）</u>， 它给出了程序的<u>*'操作语义（operational semantics）'*</u>。  
  我们定义的这个小型语言实现了一些完善语言（例如 C、C++ 和 Java） 的关键功能，包括基础的<u>可变状态</u>和<u>控制流</u>的概念。
* 我们证明了许多<u>*'元理论性质（metatheoretic properties）'*</u>，也就是 从高层次角度来说，这些性质是关于这整个语言的，而不是关于任何一段 单独的程序。这包括了：

  * 求值过程的确定性
  * 用不同方式写下的定义之间的等价关系（例如，用求值函数和求值关系来定 义算术表达式的化简规则）
  * 保证一系列程序必会停机
  * 数个实用的程序变换之正确性（从语义等价的角度来讲）
  * 程序的等价关系（在 [Equiv](https://coq-zh.github.io/SF-zh/plf-current/Equiv.html) 这一章里）。

如果在这里打住，我们已经有了一些实用的东西了：一套用来定义并讨论 程序语言和它们的功能的工具。这些工具应用于程序语言的一些关键性质， （从数学角度来讲）是严谨和灵活的，并且是易于使用的。 所有这些性质都是程序语言的设计者，编译器作者，以及用户所最关心的。 当然，这些性质中的很多是极为基础的，以至于在我们对编程语言的认知 中甚至不会把它们自然地当做“定理”来对待。但看似直观明显的属性有时候 可能会非常微妙（有时也会错得很微妙！）。

在这一卷稍后，我们将会在讨论<u>*'类型（types）'*</u>​<u>和</u>​<u>*'类型可靠性 （type soundness）'*</u>时，回归到整个语言的元理论性质研究。不过现在 我们要着眼于另外一些问题。

我们的目标是给出一些<u>*'软件形式化验证（program verification）'*</u>​<u>​ 的例子，也就是说，用 Imp 的精确定义来形式地证明某段程序符合某 个规范</u>。我们会建立一个叫做*'弗洛伊德-霍尔逻辑（Floyd-Hoare Logic）'* 的系统（一般简称 *'霍尔逻辑（Hoare Logic）'*），<u>它是 Imp 的语法构造 加上了一个通用的“验证规则”的组合，可以用来说明包含这段结构的程序 之正确性</u>。

霍尔逻辑发源于1960年代，至今为止依然是活跃的研究主题。 它用于规范和验证许多学术界与工业界广泛使用的软件系统，并处于核心地位。

霍尔逻辑组合了两个绝妙的想法：用自然的方式来编写程序的==*'规范（specifications）*==​*'* ；和一种用来证明程序正确地实现了规范的==*'复合证明技巧（compositional proof technique）'*==​==​ ​==——其中“复合”的意思是，这些证明的结构直接反映了相应程序的结构。

本章概览... 主题：

* 推理 Imp 程序*'功能正确性（functional correctness）'* 的系统方法

目标：

* 一种自然表达*'程序规范（program specifications）'*的记号
* 一种关于程序正确性的*'复合的（compositional）'*证明技巧

计划：

* 程序规范（断言／霍尔三元组）
* 证明规则
* 循环不变式
* 带标注的程序
* 例子

## 断言

要讨论程序的规范，我们需要的首先是一种在程序执行过程中某个时刻， 关于程序性质做出*'断言（assertions）'*的方法。也就是说，我们要讨论<u>执行到某处时，当时的内存状态</u>。<u>形式化地说，一项断言就是一系列关于 ​</u>​<u>**state**</u>​<u>​ 的命题。</u>

```coq
Definition Assertion := state -> Prop.
```

‍

```coq
(** **** 练习：1 星, standard, optional (assertions) 

    用中文重新表述下列断言（或者用你最喜欢的语言）。 *)

Module ExAssertions.
Definition as1 : Assertion := fun st => st X = 3.
Definition as2 : Assertion := fun st => st X <= st Y.
Definition as3 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.
Definition as4 : Assertion :=
  fun st => st Z * st Z <= st X /\
            ~ (((S (st Z)) * (S (st Z))) <= st X).
Definition as5 : Assertion :=
  fun st => st Z = max (st X) (st Y).
Definition as6 : Assertion := fun st => True.
Definition as7: Assertion := fun st => False.
(* 请在此处解答 *)
(* #GPT#
as1: 断言 as1 表示变量 X 的值在状态 st 中为 3。
as2: 断言 as2 表示变量 Y 的值不小于等于变量 X 的值。
as3: 断言 as3 表示变量 X 的值等于 3 或者变量 X 的值不大于变量 Y 的值。
as4: 断言 as4 包含两个谓词：
  第一个谓词表示变量 Z 的平方小于等于变量 X，
  第二个谓词表示变量 Z 的后继的平方大于变量 X。
as5: 断言 as5 表示变量 Z 的值等于变量 X 和变量 Y 中的最大值。
as6: 断言 as6 总是成立，它表示“不论状态是什么，它总是满足条件”。
as7: 断言 as7 总是不成立，它表示“不存在任何状态使得其满足该条件”。 *)
End ExAssertions.
```

这种写下断言的方式可能过于繁琐，理由如下： (1) 我们写的每个断言都将以 **fun** **st** **⇒** 开头； (2) 状态 **st** 是唯一我们希望用来再断言中查找变量的状态（我们将不会 讨论在同一时间的两种不同状态。 当我们非正式地讨论某些例子的时候，我们会简化一下：我们把开头的 **fun** **st** **⇒** 去掉，并且用 **X** 来代替 **st** **X** 所以，我们将把

```coq
      fun st => (st Z) * (st Z) <= m /\
                ~ ((S (st Z)) * (S (st Z)) <= m)
```

写成

```coq
      Z * Z <= m /\ ~((S Z) * (S Z) <= m).
```

这个例子也同时展示了我们将使用的另一种简便写法，我们将 在关于霍尔逻辑的章节里都使用它：在<u>非正式的断言中</u>，大写字母例如 **X**、 **Y**、**Z** 是 Imp 变量，而小写字母例如 **x**、**y**、**m**、**n** 则是一般的 Coq 变量（类型是 **nat**）。这就是当我们把非正式断言翻译成正式断言时，把 **X** 换成 **st** **X** 而留下 **m** 不变的理由。

给出两断言 **P** 与 **Q**，我们说 **P** *'蕴含'* **Q**， 写作==​ ​==​==**P**==​==​ -&gt;&gt; ​==​==**Q**==，如果当 **P** 在 **st** 下成立，**Q** 也成立。

```coq
Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.
```

这里的记号 **hoare_spec_scope** 告诉 Coq， 这个记号不是全局的， 我们打算把它用在特定的上下文里。**Open** **Scope** 告诉 Coq，这个文件就是 一个我们将采用此记号的上下文。

我们也需要一个表达断言之间“当且仅当”的蕴含关系：

```coq
Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.
```

*一些糖：*

我们实际上可以在 Coq 的正式语法中，使用我们的非正式约定来编写断言，而不需要显式地提及状态。这种技术使用了 Coq 强制转换和注释作用域（<u>就像我们在 [Imp] 中使用 [%imp] 一样 ​</u>​#TODO#​），当 [aexp]、数字和 [Prop] 出现在 [%assertion] 范围内或当 Coq 知道表达式的类型是 [Assertion] 时，它们会自动提升为 [Assertion]。

```coq
Definition Aexp : Type := state -> nat.

Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.

Definition Aexp_of_aexp (a : aexp) : Aexp := fun st => aeval st a.

Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : aexp >-> Aexp.

Arguments assert_of_Prop /.
Arguments Aexp_of_nat /.
Arguments Aexp_of_aexp /.

Bind Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Aexp.
Delimit Scope assertion_scope with assertion.

Notation assert P := (P%assertion : Assertion).
Notation mkAexp a := (a%assertion : Aexp).

Notation "~ P" := (fun st => ~ assert P st) : assertion_scope.
Notation "P /\ Q" := (fun st => assert P st /\ assert Q st) : assertion_scope.
Notation "P \/ Q" := (fun st => assert P st \/ assert Q st) : assertion_scope.
Notation "P -> Q" := (fun st => assert P st ->  assert Q st) : assertion_scope.
Notation "P <-> Q" := (fun st => assert P st <->  assert Q st) : assertion_scope.
Notation "a = b" := (fun st => mkAexp a st = mkAexp b st) : assertion_scope.
Notation "a <> b" := (fun st => mkAexp a st <> mkAexp b st) : assertion_scope.
Notation "a <= b" := (fun st => mkAexp a st <= mkAexp b st) : assertion_scope.
Notation "a < b" := (fun st => mkAexp a st < mkAexp b st) : assertion_scope.
Notation "a >= b" := (fun st => mkAexp a st >= mkAexp b st) : assertion_scope.
Notation "a > b" := (fun st => mkAexp a st > mkAexp b st) : assertion_scope.
Notation "a + b" := (fun st => mkAexp a st + mkAexp b st) : assertion_scope.
Notation "a - b" := (fun st => mkAexp a st - mkAexp b st) : assertion_scope.
Notation "a * b" := (fun st => mkAexp a st * mkAexp b st) : assertion_scope.
```

这种方法的一个小限制是，我们没有一种自动的方式来强制函数应用程序在断言中适当地使用状态。相反，我们使用显式的 [ap] 运算符来提升函数。

```coq
Definition ap {X} (f : nat -> X) (x : Aexp) :=
  fun st => f (x st).

Definition ap2 {X} (f : nat -> nat -> X) (x : Aexp) (y : Aexp) (st : state) :=
  f (x st) (y st).

Module ExPrettyAssertions.
Definition as1 : Assertion := X = 3.
Definition as2 : Assertion := X <= Y.
Definition as3 : Assertion := X = 3 \/ X <= Y.
Definition as4 : Assertion :=
  Z * Z <= X /\
            ~ (((ap S Z) * (ap S Z)) <= X).
Definition as5 : Assertion :=
  Z = ap2 max X Y.
Definition as6 : Assertion := True.
Definition as7 : Assertion := False.
End ExPrettyAssertions.
```

‍

## 霍尔三元组

接下来，我们需要一种描述命令行为的方式。

广泛而言，一个命令的行为就是把一个状态转变成另一个状态，所以 我们可以自然地<u>通过命令运行前后的断言来描述一个命令</u>。

* “如果命令 **c** 在一个复合断言 **P** 的状态开始，并且如果 **c** 最终在一个结束状态停机，这个结束状态会满足断言 **Q**。”

这样的描述叫做==*'霍尔三元组（Hoare Triple）'*==。断言 **P** 叫做 **c** 的==*'前置条件（precondition）'*==，而 **Q** 叫做==​ ​==​==*'后置条件（postcondition）'*==。

形式化地：

```coq
Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st'  ->
     P st  ->
     Q st'.
```

因为我们将会在霍尔三元组上做很多研究，所以一个紧凑的记号是非常便 利的：  
       {**{**P}**}** **c** {**{**Q}**}.**

（<u>传统的记号是 ​</u>​<u>**{**</u>​<u>P</u>​<u>**}**</u>​<u>​ ​</u>​<u>**c**</u>​<u>​ ​</u>​<u>**{**</u>​<u>Q</u>​<u>**}**</u>，不过单花括号已经被用在 Coq 中其 它东西上了。

‍

```coq
   1) {{True}} c {{X = 5}}
当程序执行c时，如果X的值为5，则前提条件True成立。
   2) {{X = m}} c {{X = m + 5)}}
当程序执行c时，如果X的初始值为m，则程序结束后X的值为m+5。
   3) {{X <= Y}} c {{Y <= X}}
当程序执行c时，如果X的值小于等于Y，则程序结束后Y的值大于等于X。
   4) {{True}} c {{False}}
？当程序执行c时，不停机
   5) {{X = m}}
      c
      {{Y = real_fact m}}
当程序执行c时，如果X的初始值为m，则程序结束后Y的值为实际上的m的因子。
   6) {{X = m}}
      c
      {{(Z * Z) <= m /\ ~ (((S Z) * (S Z)) <= m)}}
当程序执行c时，如果X的初始值为m，则程序结束时Z的平方小于等于 m 且(S Z)的平方不大于m。  

   1) {{True}} X ::= 5 {{X = 5}}
成立，5赋值给X后X的值为5。
   2) {{X = 2}} X ::= X + 1 {{X = 3}}
成立，2加1等于3，因此X的值变为3。
   3) {{True}} X ::= 5;; Y ::= 0 {{X = 5}}
成立，先将X的值赋为5，接着将Y赋值为0，最终X的值为5。
   4) {{X = 2 /\ X = 3}} X ::= 5 {{X = 0}}
不成立，由前提条件得知X的值不能既为2又为3，因此该霍尔三元组不成立。
   5) {{True}} SKIP {{False}}
不成立，SKIP执行时不会改变程序状态，断言的结论False非真。
   6) {{False}} SKIP {{True}}
？成立，SKIP执行时不会改变程序状态，而前提条件False永远不成立，所以该霍尔三元组成立。
   7) {{True}} WHILE true DO SKIP END {{False}}
？成立，这个循环会一直执行下去，因此后面的断言False非真
   8) {{X = 0}}
        WHILE X = 0 DO X ::= X + 1 END
      {{X = 1}}
成立，X的初始值为0，进入while循环后将X的值设为1，因此在while循环结束时X的值为1，符合断言的结论。
   9) {{X = 1}}
        WHILE ~(X = 0) DO X ::= X + 1 END
      {{X = 100}}
不成立。
```

为了热身，这里有两个关于霍尔三元组的简单定理。 （确保看懂了这些再继续。）

```coq
Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  apply H.  Qed.
(* Q 恒真，则霍尔三元组成立 *)

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~ (P st)) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  unfold not in H. apply H in HP.
  inversion HP.  Qed.
(* P 恒假，则霍尔三元组成立 *)
```

‍

## 证明规则

霍尔逻辑的目标是提供一种*_组合的_* 方法， 用来证明特定三元组的正确性。 也即，我们希望一段程序的正确性证明的结构反映程序本身。 为了达成这个目的，在下面的小节中，我们为不同语法形式的 Imp 命令引入不同的推理规则：<u>关于赋值的、关于顺序执行的、 关于条件执行的等等。还有一些“结构的”规则用来组合它们</u>。<u>​ 用这种组合的方式，我们甚至不用展开 ​</u>​<u>**hoare_triple**</u>​<u>​ 的定义也能证明 一段程序是正确的。</u>

### 赋值

赋值是霍尔逻辑的规则中最基础的一个。它的原理如下。

考虑这个成立的霍尔三元组：

```coq
       {{ Y = 1 }}  X ::= Y  {{ X = 1 }}
```

用中文讲：如果我们从一个 **Y** 是 **1** 的状态开始， 然后我们把 **Y** 赋给 **X**，我们最终会得到一个 **X** 是 **1** 的状态。 也即，“等于 **1**”这个属性被从 **Y** 传递给了 **X**。

相似地，在

```coq
       {{ Y + Z = 1 }}  X ::= Y + Z  {{ X = 1 }}
```

里，同样的属性（等于 **1**）被从赋值命令的右侧 **Y** **+** **Z** 传递给了 **X**。

更一般地, 如果 **a** 是*'任意'*算术表达式，那么

```coq
       {{ a = 1 }}  X ::= a  {{ X = 1 }}
```

是一个成立的霍尔三元组。

甚至更一般地，为了得到 **Q** 在 **X** ::= **a** 后仍然成立，我们需要先有 **Q** 在 **X** ::= **a** 前成立，不过*'所有在 ​*​***Q***​*​ 中出现的'* **X** 被 替换为 **a**。这给出了霍尔逻辑中赋值的规则

```coq
      {{ Q [X |-> a] }} X ::= a {{ Q }}
```

其中 `Q [X |-> a]` 读作 “在 **Q** 中把 **X** 换成 **a**”。

例如，下列这些是赋值规则正确的应用：

```coq
      {{ (X <= 5) [X |-> X + 1]
         i.e., X + 1 <= 5 }}
      X ::= X + 1
      {{ X <= 5 }}

      {{ (X = 3) [X |-> 3]
         i.e., 3 = 3 }}
      X ::= 3
      {{ X = 3 }}

      {{ (0 <= X /\ X <= 5) [X |-> 3]
         i.e., (0 <= 3 /\ 3 <= 5) }}
      X ::= 3
      {{ 0 <= X /\ X <= 5 }}
```

为了形式化这个规则，我们必须先把“在一个断言中将 Imp 变量替换为一个 表达式” 的概念形式化，我们把这叫做“断言替换”，或者是 **assn_sub**。 也就是说，给出命题 **P**、变量 **X**、算术表达式 **a**，我们想要生成一个 新的命题 **P'**，它和 **P** 一样，不过 **P'** 应该用 **a** 来取代所有 **P** 提及 **X** 之处。

因为 **P** 是一个任意的 Coq 断言，我们不能直接“编辑”它的文本部分。不 过，我们可以通过将 **P** 在下述新的状态中计算来达到相同的效果：

‍

‍

‍

‍

‍

‍

‍

‍

‍
