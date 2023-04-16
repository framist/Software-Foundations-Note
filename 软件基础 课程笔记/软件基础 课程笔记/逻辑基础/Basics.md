---
title: Basics
date: 2023-04-16T16:04:11Z
lastmod: 2023-04-16T16:10:59Z
---

# Basics

# Coq 函数式编程    (Basics)

* [引言](https://coq-zh.github.io/SF-zh/lf-current/Basics.html#lab19)
* [数据与函数](https://coq-zh.github.io/SF-zh/lf-current/Basics.html#lab20)

  * [枚举类型](https://coq-zh.github.io/SF-zh/lf-current/Basics.html#lab21)
  * [一周七日](https://coq-zh.github.io/SF-zh/lf-current/Basics.html#lab22)
  * [作业提交指南](https://coq-zh.github.io/SF-zh/lf-current/Basics.html#lab23)
  * [布尔值](https://coq-zh.github.io/SF-zh/lf-current/Basics.html#lab24)
  * [类型](https://coq-zh.github.io/SF-zh/lf-current/Basics.html#lab27)
  * [由旧类型构造新类型](https://coq-zh.github.io/SF-zh/lf-current/Basics.html#lab28)
  * [元组](https://coq-zh.github.io/SF-zh/lf-current/Basics.html#lab29)
  * [模块](https://coq-zh.github.io/SF-zh/lf-current/Basics.html#lab30)
  * [数值](https://coq-zh.github.io/SF-zh/lf-current/Basics.html#lab31)
* [基于化简的证明](https://coq-zh.github.io/SF-zh/lf-current/Basics.html#lab34)
* [基于改写的证明](https://coq-zh.github.io/SF-zh/lf-current/Basics.html#lab35)
* [利用分类讨论来证明](https://coq-zh.github.io/SF-zh/lf-current/Basics.html#lab38)
* [关于记法的更多内容 (可选)](https://coq-zh.github.io/SF-zh/lf-current/Basics.html#lab41)
* [不动点 ](https://coq-zh.github.io/SF-zh/lf-current/Basics.html#lab42)​**[Fixpoint](https://coq-zh.github.io/SF-zh/lf-current/Basics.html#lab42)**​[ 和结构化递归 (可选)](https://coq-zh.github.io/SF-zh/lf-current/Basics.html#lab42)
* [更多练习](https://coq-zh.github.io/SF-zh/lf-current/Basics.html#lab44)

## 数据与函数

一周七日

```coq
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

Compute (next_weekday friday).
(* ==> monday : day *)
Compute (next_weekday (next_weekday saturday)).
(* ==> tuesday : day *)

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.
```

‍

​#TODO#​ 第三，我们可以让 Coq 从 **Definition** 中*'提取（Extract）'* 出用其它更加常规的编程语言编写的程序 （如 OCaml、Scheme、Haskell 等），它们拥有高性能的编译器。 这种能力非常有用，我们可以通过它将 Gallina 编写的 *'证明正确'* 的算法转译成高效的机器码。（诚然，我们必须信任 OCaml / Haskell / Scheme 的编译器，以及 Coq 提取工具自身的正确性，然而比起现在大多数软件的开发方式， 这也是很大的进步了。）实际上，这就是 Coq 最主要的使用方式之一。 在之后的章节中我们会回到这一主题上来。

```coq
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
```

Coq 实际上支持对_任何_归纳定义的双子句表达式使用 "if" 表达式 （不过恰巧在这里该表达式被称为 **bool**）。<u>当条件求值后得到的是第一个子句的 “构造子” (constructor)，那么条件就会被认为是 “真” ​</u>​**true**（不过恰巧 在这里第一个分支的构造子被称为 “真” **true**，并且如果求值后得到的是第二个子句， 那么条件就被认为是 “假” **false**）。

‍

如果在被 ==**Check**== 的表达式后加上一个分号和你想验证的类型，那么 Coq 会 验证该表达式是否属于你提供的类型。当两者不一致时，Coq 会报错并终止执行。

```coq
Check true
    : bool.
Check (negb true)
    : bool.
```

‍

### 由旧类型构造新类型

```coq
Inductive rgb : Type :=
  | red
  | green
  | blue.
Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).
```

像 **red**、**green**、**blue**、**black**、**white** 以及 **primary**（还有 **true**、**false**、**monday** 等）这样的原子标识符叫做*'*​==*构造子（Constructor）*==​*'*。

我们可以用它们来构建*'构造子表达式（Constructor Expression）'*， 其中每一个要么是一个简单的构造子，要么就是一个构造子应用于一个或多个参数 （每个这样的参数也都是构造子表达式）。

我们来仔细研究一下。每个归纳定义的类型（如 **day**、**bool**、**rgb**、**color** 等） 都描述了一组由*'构造子'*构成的*'构造子表达式'*。

* 我们从有限的一组*'构造子'*开始。例如 **red**、**primary**、**true**、**false**、**monday** 等等都是构造子。
* *'构造子表达式'*通过将构造子应用到一个或多个构造子表达式上构成。例如 **red**、**true**、**primary**、**primary** **red**、**red** **primary**、**red** **true**、 **primary** **(**primary **primary**) 等等
* 每个 **Inductive** 定义都刻画了一个构造子表达式的子集并赋予了它们名字，如 **bool**、**rgb** 或 **color**。

具体来说，**rgb** 和 **color** 的定义描述了如何构造这两个集合中的构造子表达式：

* 构造子表达式 **red**、**green** 和 **blue** 属于集合 **rgb**；
* 构造子表达式 **black** 和 **white** 属于集合 **color**；
* 若 **p** 是属于 **rgb** 的构造子表达式，则 **primary** **p**（读作“构造子 **primary** 应用于参数 **p**）是属于集合 **color** 的构造子表达式；且
* 通过这些方式构造的构造子表达式*'只属于'*集合 **rgb** 和 **color**。

我们可以像之前的 **day** 和 **bool** 那样用模式匹配为 **color** 定义函数。

```coq
Definition monochrome (c : color) : bool :=
  match c with
  | black ⇒ true
  | white ⇒ true
  | primary p ⇒ false
  end.
```

鉴于 **primary** 构造子接收一个参数，匹配到 **primary** 的模式应当带有一个 变量或常量。变量可以取任意名称，如上文所示；常量需有适当的类型，例如：

```coq
Definition isred (c : color) : bool :=
  match c with
  | black ⇒ false
  | white ⇒ false
  | primary red ⇒ true
  | primary _ ⇒ false
  end.
```

这里的模式 **primary** **_** 是“构造子 **primary** 应用到除 **red** 之外的任何 **rgb** 构造子上”的简写形式（通配模式 **_** 的效果与 **monochrome** 定义中的哑（dummy）模式变量 **p** 相同。）

### 元组

一个多参数的单构造子可以用来创建元组类型。例如，为了让一个 半字节（nybble）表示四个比特。我们首先定义一个 **bit** 数据类型 来类比 **bool** 数据。并且使用 **B**​~0~ 和 **B**​~1~ 两种构造子来表示其可能的取值。 最后定义 **nybble** 这种数据类型，也就是一个四比特的元组。

```coq
Inductive bit : Type :=
  | B0
  | B1.
Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).
Check (bits B1 B0 B1 B0)
    : nybble.
```

这里的 **bit** 构造子起到了对它内容的包装作用。 解包可以通过模式匹配来实现，就如同下面的 **all_zero** 函数一样， 其通过解包来验证一个半字节的所有比特是否都为 **B**​~0~。 我们用*'通配符'* 来避免创建不需要的变量名。

```coq
Definition all_zero (nb : nybble) : bool :=
  match nb with
    | (bits B0 B0 B0 B0) ⇒ true
    | (bits _ _ _ _) ⇒ false
  end.
Compute (all_zero (bits B1 B0 B1 B0)).
(* ===> false : bool *)
Compute (all_zero (bits B0 B0 B0 B0)).
(* ===> true : bool *)
```

### 模块

Coq 提供了*'模块系统'*来帮助组织大规模的开发。在本课程中， 我们不太会用到这方面的特性。不过其中有一点非常有用： 如果我们将一组定义放在 **Module** **X** 和 **End** **X** 标记之间，那么在文件中的 **End** 之后，我们就可以通过像 **X.foo** 这样的名字来引用，而不必直接用 **foo** 了。在这里，我们通过此特性在内部模块中引入了 **nat** 类型的定义， 这样就不会覆盖标准库中的同名定义了（我们会在本书后面的部分中使用它， 因为它提供了一些简便的特殊记法。）

```coq
Module NatPlayground.
  (* ... *)
End NatPlayground.
```

### 数值

```coq
Inductive nat : Type :=
  | O
  | S (n : nat).
```

* 构造子表达式 \[O\] 属于集合 \[nat\]；
* 如果 \[n\] 是属于集合 \[nat\] 的构造子表达式，  
  那么 \[S n\] 也是属于集合 \[nat\] 的构造子表达式；并且
* 只有以这两种产生的方式构造字表达式才属于集合 \[nat\]。

为了让自然数使用起来更加自然，Coq 内建了一小部分解析打印功能： 普通的十进制数可视为“一进制”自然数的另一种记法，以代替 **S** 与 **O** 构造子； 反过来，Coq 也会默认将自然数打印为十进制形式：

```coq
Check (S (S (S (S O)))).
(* ===> 4 : nat *)

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Compute (minustwo 4).
(* ===> 2 : nat *)
```

```coq
Check S        : nat->nat.
Check pred     : nat->nat.
Check minustwo : nat->nat.
```

以上三个东西均可作用于自然数，并产生自然数结果，但第一个 **S** 与后两者有本质区别：**pred** 和 **minustwo** 这类函数是通过给定的*'计算规则'*定义的—— 例如 **pred** 的定义表明 **pred** **2** 可化简为 **1**——但 **S** 的定义不包含此类行为。 虽然 **S** 可以作用于参数这点与函数*'相似'*，但其作用仅限于构造数字，而并不用于计算。（考虑标准的十进制数：数字 **1** 不代表任何计算，只表示一部分数据。 用 **111** 指代数字一百一十一，实则使用三个 **1** 符号表示此数各位。）

‍

简单的模式匹配不足以描述很多有趣的数值运算，我们还需要递归定义。

 关键字 ==**Fixpoint**== 可用于定义此类函数。

> Fixpoint 其实跟 Y组合子（Y Combinator）差不多？

```coq
Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Compute (plus 3 2).
(* ===> 5 : nat *)

(** 你可以在两个表达式之间添加逗号来同时匹配它们：*)

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O   , _    => O
  | S _ , O    => n
  | S n', S m' => minus n' m'
  end.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.
```

```coq
Notation "x + y" := (plus x y)
Notation "x - y" := (minus x y)
Notation "x * y" := (mult x y)
Notation "x =? y" := (eqb x y) 
Notation "x <=? y" := (leb x y)
Notation "x <? y" := (ltb x y) 
```

## 基于化简的证明

```coq
Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.
```

首先，我们使用了关键字 **Theorem** 而非 **Example**。这种差别纯粹是风格问题； 在 Coq 中，<u>关键字 ​</u>​<u>**Example**</u>​<u>​ 和 ​</u>​<u>**Theorem**</u>​<u>（以及其它一些，包括 ​</u>​<u>**Lemma**</u>​<u>、</u>​<u>**Fact**</u>​<u>​ 和 ​</u>​<u>**Remark**</u>​<u>）都表示完全一样的东西。</u>

其次，我们==增加了量词 ​==​==**∀**==​==​ ​==​==**n**==​==:==​==**nat**==，因此我们的定理讨论了*'所有的'* 自然数 **n**。 在非形式化的证明中，为了证明这种形式的定理，我们通常会说“*'假设'* 存在一个任意自然数 **n**...”。而在形式化证明中，这是用 **intros** **n** 来实现的，它会将量词从证明目标转移到当前假设的*'上下文'*中。 注意在 **intros** 从句中，我们可以使用别的标识符来代替 **n**

关键字 **intros**、**simpl** 和 **reflexivity** 都是*'策略（Tactic）'*的例子。 策略是一条可以用在 **Proof**（证明）和 **Qed**（证毕）之间的指令，它告诉 Coq 如何来检验我们所下的一些断言的正确性。

## 基于改写的证明

```coq
Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  (* 将两个量词移到上下文中： *)
  intros n m.
  (* 将前提移到上下文中： *)
  intros H.
  (* 用前提改写目标： *)
  rewrite -> H.
  reflexivity.  Qed.
```

该定理并未对自然数 **n** 和 **m** 所有可能的值做全称断言，而是讨论了仅当 **n** **=** **m** 时这一更加特定情况。箭头符号读作“==蕴含==”。#TODO#​ 蕴含与前提的关系？

==**intros**== 策略用来将这三条前提从证明目标 移到当前上下文的假设中。

用来告诉 Coq 执行这种替换的策略叫做*'改写'* **rewrite**。

==**rewrite**== 中的箭头与蕴含无关：它指示 Coq 从左往右地应用改写。 若要从右往左改写，可以使用 `rewrite <-`​

**Check** 命令也可用来检查以前声明的引理和定理。

‍

## 利用分类讨论来证明

用 **Abort** 指令来放弃证明。

告诉 Coq 分别对 **n** **=** **0** 和 **n** **=** **S** **n'** 这两种情况进行分析的策略，叫做 **destruct**。

```coq
Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity.   Qed.
```

==**destruct**== 策略会生成*两个*子目标，为了让 Coq 认可这个定理， 我们必须接下来证明这两个子目标。

as **[|** **n'**] 这种标注被称为 *'引入模式'*。它告诉 Coq 应当在每个子目标中 使用什么样的变量名。总体而言，在方括号之间的是一个由 **|** 隔开的 *'列表的列表'*（译者注：list of lists）。在上面的例子中，第一个元素是 一个空列表，因为 **O** 构造子是一个空构造子（它没有任何参数）。 第二个元素提供了包含单个变量名 **n'** 的列表，因为 **S** 是一个单构造子。

在每个子目标中，Coq 会记录这个子目标中关于 **n** 的假设，**n** **=** **0** 还是 对于某个 n', **n** **=** **S** **n'**。而 **eqn**:**E** 记号则告知 Coq 以 **E** 来命名这些 假设。省略 **eqn**:**E** 会导致 Coq 省略这些假设。这种省略能够使得一些不需要 显式用到这类假设的证明显得更加流畅。但在实践中最好还是保留他们， 因为他们可以作为一种说明文档来在证明过程中指引你。

第二行和第三行中的 **-** 符号叫做*'标号'*，它标明了这两个生成的子目标所对应的证明部分。 （译注：此处的“标号”应理解为一个项目列表中每个 *'条目'* 前的小标记，如 ‣ 或 •。） 标号后面的证明脚本是一个子目标的完整证明。在本例中，每个子目标都简单地使用 **reflexivity** 完成了证明。通常，**reflexivity** 本身会执行一些化简操作。 例如，第二段证明将 **at** **(**S **n'** **+** **1)** **0** 化简成 **false**，是通过先将 **(**S **n'** **+** **1)** 转写成 **S** **(**n' **+** **1)**，接着展开 **beq_nat**，之后再化简 **match** 完成的。

**destruct** 策略可用于任何归纳定义的数据类型。比如，我们接下来会用它来证明 布尔值的取反是==对合（Involutive）==的 —— 即，取反是自身的逆运算。

```coq
Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity.  Qed.
```

注意这里的 **destruct** 没有 **as** 子句，因为此处 **destruct** 生成的子分类均无需绑定任何变量，因此也就不必指定名字。 实际上，我们也可以省略 *'任何'* **destruct** 中的 **as** 子句， Coq 会自动填上变量名。不过这通常是个坏习惯，因为如果任其自由决定的话， Coq 经常会选择一些容易令人混淆的名字。

有时在一个子目标内调用 **destruct**，产生出更多的*证明义务（Proof Obligation）* 也非常有用。这时候，我们使用不同的标号来标记目标的不同“层级”，比如：

```coq
Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.
```

除了 \[-\] 和 \[+\] 之外，还可以使用 \[\*\]（星号）或任何重复的标号符（如 \[--\] 或 \[\*\*\*\]）作为标号。我们也可以用花括号将每个子证明目标括起来：花括号还允许我们在一个证明中的多个层级下使用同一个标号。

```coq
Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
Qed.
```

或许你已经注意到了，    很多证明在引入变量之后会立即对它进行情况分析：

​`intros x y. destruct y as [|y] eqn:E.`​

这种写法是如此的常见以至于 Coq 为它提供了一种简写：我们可以在引入 一个变量的同时对他使用*'引入模式'*来进行分类讨论。例如，下面是一个对 **plus_1_neq_0** 的更简短证明。（这种简写的缺点也显而易见， 我们无法再记录在每个子目标中所使用的假设，而之前我们可以通过 **eqn**:**E** 将它们标注出来。）

```coq
Theorem plus_1_neq_0' : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.  Qed.
```

如果没有需要命名的构造子参数，我们只需写上 **[]** 即可进行情况分析。

```coq
Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
```

```coq
(** **** 练习：2 星, standard (andb_true_elim2) 

    证明以下断言, 当使用 [destruct] 时请用标号标出情况（以及子情况）。 *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec. 
    + simpl. reflexivity.
    + simpl. intros H. rewrite -> H. reflexivity.
  - destruct c eqn:Ec. 
    + simpl. reflexivity.
    + simpl. intros H. rewrite -> H. reflexivity.
Qed.
```

‍

## 关于记法的更多内容 (可选)

<u>专业提示：Coq 的符号机制不是特别强大，别期望太多。</u>

## 不动点 **Fixpoint** 和结构化递归 (可选)

```coq
(** **** 练习：2 星, standard, optional (decreasing) 

    为了更好的理解这一点，请尝试写一个对于所有输入都_的确_终止的 [Fixpoint]
    定义。但这个定义需要违背上述的限制，以此来让 Coq 拒绝。（如果您决定将这个可选
    练习作为作业，请确保您将您的解答注释掉以防止 Coq 拒绝执行整个文件。）
TODO : 参考来的答案  *)
Fixpoint not_accepted (n : nat) : nat :=
  match n with
  | O => not_accepted (S O)
  | S O => S O
  | S n' => S (not_accepted n')
  end.
```

​#TODO#​

## 更多练习

Each SF chapter comes with a tester file (e.g. **BasicsTest.v**), containing scripts that check most of the exercises. You can run **make** **BasicsTest.vo** in a terminal and check its output to make sure you didn't miss anything.

make *详细配置方案参考下一章（Induction）开头*

这些针对单增函数和二进制转换函数的“单元测试”可以验算你的定义的正确性。 当然，这些单元测试并不能确保你的定义在所有输入下都是正确的！我们在下一章的末尾会重新回到这个话题。

‍

‍
