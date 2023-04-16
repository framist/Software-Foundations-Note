---
title: Poly
date: 2023-04-16T16:08:21Z
lastmod: 2023-04-16T16:08:49Z
---

# Poly

# 多态与高阶函数    (Poly)

* [多态](https://coq-zh.github.io/SF-zh/lf-current/Poly.html#lab100)

  * [多态列表](https://coq-zh.github.io/SF-zh/lf-current/Poly.html#lab101)
  * [多态序对](https://coq-zh.github.io/SF-zh/lf-current/Poly.html#lab110)
  * [多态候选](https://coq-zh.github.io/SF-zh/lf-current/Poly.html#lab113)
* [函数作为数据](https://coq-zh.github.io/SF-zh/lf-current/Poly.html#lab115)

  * [高阶函数](https://coq-zh.github.io/SF-zh/lf-current/Poly.html#lab116)
  * [过滤器](https://coq-zh.github.io/SF-zh/lf-current/Poly.html#lab117)
  * [匿名函数](https://coq-zh.github.io/SF-zh/lf-current/Poly.html#lab118)
  * [映射](https://coq-zh.github.io/SF-zh/lf-current/Poly.html#lab121)
  * [折叠](https://coq-zh.github.io/SF-zh/lf-current/Poly.html#lab126)
  * [用函数构造函数](https://coq-zh.github.io/SF-zh/lf-current/Poly.html#lab128)
* [附加练习](https://coq-zh.github.io/SF-zh/lf-current/Poly.html#lab129)

‍

‍

在本章中，我们会继续发展函数式编程的基本概念，其中最关键的新概念就是 *'多态'*（在所处理的数据类型上抽象出函数）和*'高阶函数'*（函数作为数据）。

## 多态

*嗯...一种抽象手段*

### 多态列表

为避免这些重复，Coq 支持定义*'多态'*归纳类型。 例如，以下就是*'多态列表'*数据类型。

```coq
Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).
```

这和上一章中 **natlist** 的定义基本一样，只是将 **cons** 构造子的 **nat** 参数换成了任意的类型 **X**，函数头的第一行添加了 **X** 的绑定， 而构造子类型中的 **natlist** 则换成了 **list** **X**。（我们可以重用构造子名 **nil** 和 **cons**，因为之前定义的 **natlist** 在当前作用之外的一个 **Module** 中。）

list 本身又是什么类型？一种不错的思路就是把 **list** 当做从 **Type** 类型到 **Inductive** 归纳定义的*'函数'*；或者换种更简明的思路，即 **list** 是个从 **Type** 类型到 **Type** 类型的函数。对于任何特定的类型 **X**， 类型 **list** **X** 是一个 **Inductive** 归纳定义的，元素类型为 **X** 的列表的集合。

​`Check list : Type -> Type.`​

**list** 的定义中的参数 **X** 自动 成为构造子 **nil** 和 **cons** 的参数 —— 也就是说，**nil** 和 **cons** 在这里是多态 的构造子；现在我们调用它们的时候必须要提供一个参数，就是它们要构造的列表的具 体类型。例如，**nil** **nat** 构造的是 **nat** 类型的空列表。

```coq
Check (nil nat) : list nat.
Check (cons nat 3 (nil nat)) : list nat.
```

**nil** 的类型会是什么呢？也许我们可以（根据定义）说它是 **list** **X**， 不过这样它就不是接受 **X** 返回 **list** 的函数了。再提出一种：**Type** **→** **list** **X** 并没有解释 **X** 是什么，**(**X **:** **Type**) **→** **list** **X** 则比较接近。 Coq 对这种情况的记法为 **∀** **X** **:** **Type**, **list** **X**：

```coq
Check nil : forall X : Type, list X.
Check cons : forall X : Type, X -> list X -> list X.
```

如果在每次使用列表构造子时，都要为它提供类型参数，那样会很麻烦。 不过我们很快就会看到如何省去这种麻烦。

现在我们可以回过头来定义之前写下的列表处理函数的多态版本了。 例如 **repeat**：

```coq
Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.
```

#### 类型标注的推断

Coq 可以使用*'类型推断'* 基于它们的使用方式来推出 **X**、**x** 和 **count** 一定是什么类型。例如， 由于 **X** 是作为 **cons** 的参数使用的，因此它必定是个 **Type** 类型， 因为 **cons** 期望一个 **Type** 作为其第一个参数，而用 **0** 和 **S** 来匹配 **count** 意味着它必须是个 **nat**，诸如此类。

```coq
Fixpoint repeat' X x count : list X :=
  match count with
  | 0        => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Check repeat'
  : forall X : Type, X -> nat -> list X.
```

#### 类型参数的推断

在任何我们可以写类型参数的地方，我们都可 以将类型参数写为 “洞” ==**_**==，可以看做是说 “请 Coq 自行找出这里应该填什么。” 更确切地说，当 Coq 遇到 **_** 时，它会尝试*'统一'*所有的局部变量信息， 包括函数应当应用到的类型，其它参数的类型，以及应用函数的上下文中期望的类型， 以此来确定 **_** 处应当填入的具体类型。

```coq
repeat' (X : _) (x : _) (count : _) : list X

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0        => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).
(** ……我们可以用洞来这样写： *)
Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).
```

‍

#### 隐式参数

我们甚至可以通过告诉 Coq *'总是'*推断给定函数的类型参数来在大多数情况下 直接避免写 **_**。

==Arguments== 用于指令指定函数或构造子的名字并列出其参数名， 花括号中的任何参数都会被视作隐式参数。（如果定义中的某个参数没有名字， 那么它可以用通配模式 **_** 来标记。这种情况常见于构造子中。）

```coq
Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.
```

现在我们完全不用提供类型参数了：

```coq
Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
```

此外，我们还可以在定义函数时就声明隐式参数，只需要将某个参数两边的圆括号换成花括号。例如：

```coq
Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat''' x count')
  end.
```

（注意我们现在甚至不必在 **repeat'''** 的递归调用中提供类型参数了， 实际上提供了反而是无效的，因为 Coq 并不想要它。）

我们会尽可能使用最后一种风格，不过还会继续在 **Inductive** 构造子中使用显式的 **Argument** 声明。原因在于如果将归纳类型的形参标为隐式的话， 不仅构造子的类型会变成隐式的，类型本身也会变成隐式的。例如， 考虑以下 **list** 类型的另一种定义：

```coq
Inductive list' {X:Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').
```

<u>由于 ​</u>​<u>**X**</u>​<u>​ 在包括 ​</u>​<u>**list'**</u>​<u>​ 本身的</u>​<u>*'整个'*</u>​<u>归纳定义中都是隐式声明的， 因此当我们讨论数值、布尔值或其它任何类型的列表时，都只能写 ​</u>​<u>**list'**</u>​<u>， 而写不了 ​</u>​<u>**list'**</u>​<u>​ ​</u>​<u>**nat**</u>​<u>、</u>​<u>**list'**</u>​<u>​ ​</u>​<u>**bool**</u>​<u>​ 等等，这样就有点过分了。</u>

作为本节的收尾，我们为新的多态列表重新实现几个其它的标准列表函数...

```coq
Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.
```

‍

‍

#### 显式提供类型参数

用 **Implicit** （隐式）将参数声明为隐式的会有个小问题：Coq 偶尔会没有足够的局部信息来确定类型参数。此时，我们需要告诉 Coq 这次我们会显示地给出参数。例如，假设我们写了如下定义：

```coq
Fail Definition mynil := nil.
(* The command has indeed failed with message:
The following term contains unresolved implicit arguments:
  nil
More precisely: 
- ?X: Cannot infer the implicit parameter X of nil whose type is "Type". *)
```

（**Definition** 前面的 **Fail** 限定符可用于*'任何'*指令， 它的作用是确保该指令在执行时确实会失败。如果该指令失败了，Coq 就会打印出相应的错误信息，不过之后会继续处理文件中剩下的部分。）

在这里，Coq 给出了一条错误信息，因为它不知道应该为 **nil** 提供何种类型。 我们可以为它提供个显式的类型声明来帮助它，这样 Coq 在“应用”**nil** 时就有更多可用的信息了：

```coq
Definition mynil : list nat := nil.
```

此外，我们还可以在函数名前加上==前缀 ​==​==**@**==​==​ ​==来强制将隐式参数变成显式的：

```coq
Check @nil : forall X : Type, list X.
Definition mynil' := @nil nat.
```

使用参数推断和隐式参数，我们可以为列表定义和前面一样的简便记法。 由于我们让构造子的的类型参数变成了隐式的，因此 Coq 就知道在我们使用该记法时自动推断它们了。

```coq
Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(** 现在列表就能写成我们希望的方式了： *)

Definition list123''' := [1; 2; 3].
```

‍

### 多态序对

按照相同的模式，我们在上一章中给出的数值序对的定义可被推广为 *'*​==*多态序对（Polymorphic Pairs）*==​*'*，它通常叫做==*'积（Products）*==​*'*：

```coq
Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y} _ _.
```

和列表一样，我们也可以将类型参数定义成隐式的， 并以此定义类似的具体记法：

```coq
Notation "( x , y )" := (pair x y).
```

我们也可以使用 **Notation** 来定义标准的*'积类型（Product Types）'*记法：

```coq
Notation "X * Y" := (prod X Y) : type_scope.
```

（标注 **:** ==**type_scope**== 会告诉 Coq 该缩写只能在解析类型而非表达式时使用。 这避免了与乘法符号的冲突。)

一开始会很容易混淆 **(**x**,**y**)** 和 **X**×**Y**。不过要记住 **(**x**,**y**)** 是一个*'值'*，它由两个其它的值构造得来；而 **X**×**Y** 是一个*'类型'*， 它由两个其它的类型构造得来。如果 **x** 的类型为 **X** 而 **y** 的类型为 **Y**， 那么 **(**x**,**y**)** 的类型就是 **X**×**Y**。

<u>第一元（first）和第二元（second）的射影函数（Projection Functions）</u>现在看起来和其它函数式编程语言中的很像了：

```coq
Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.
```

​#GPT#​ 射影函数是一种数学概念，它指的是将一个点或一个向量从一个空间映射到另一个空间的函数。射影函数可以帮助人们在不同的空间之间建立联系，从而使得某些概念变得更加容易理解和推广。例如，在几何学中，人们可以使用射影函数来投影一个三维平面上的图形到二维平面上，从而使得图形的某些特征变得更加易于理解。

以下函数接受两个列表，并将它们结合成一个序对的列表。 在其它函数式语言中，它通常被称作 **zip**。我们为了与 Coq 的标准库保持一致， 将它命名为 **combine**。

```coq
Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.
```

函数 **split** 是 **combine** 的右逆（right inverse）： 它接受一个序对的列表并返回一个列表的序对。 在很多函数式语言中，它被称作 **unzip**。

```coq
Definition append_list_pair {X Y : Type} 
                            (lp1 : (list X) * (list Y)) 
                            (lp2 : (list X) * (list Y)) : (list X) * (list Y) :=
((fst lp1) ++ (fst lp2), (snd lp1) ++ (snd lp2)).

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  (* 将本行替换成 ":= _你的_定义_ ." *)
  match l with
  | [] => ([], [])
  | (h1, h2) :: tail => append_list_pair ([h1], [h2]) (split tail)
  end.
```

‍

‍

### 多态候选

最后一种要介绍的多态类型是*'多态候选（Polymorphic Options）'*, 它推广了上一章中的 **natoption**（由于我们之后要用标准库中定义的 **option** 版本，因此这里的定义我们把它放在模块中）：

```coq
Module OptionPlayground.

Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X} _.
Arguments None {X}.
```

现在我们可以重写 **nth_error** 函数来让它适用于任何类型的列表了。

```coq
Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | [] => None
  | a :: l' => if n =? O then Some a else nth_error l' (pred n)
  end.
```

‍

‍

## 函数作为数据

和大部分现代编程语言一样，特别是“函数式”的语言，包括 OCaml、Haskell、 Racket、Scala、Clojure 等，Coq 也将函数视作“一等公民（First-Class Citizens）”， 即允许将它们作为参数传入其它函数、作为结果返回、以及存储在数据结构中等等。

‍

### 高阶函数

用于操作其它函数的函数通常叫做*'高阶函数'*。以下是简单的示例：

```coq
Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).
```

注意到下面括号的使用 ((20221203193402-angfulj '突然发现多输入函数的类型的形式是连蕴含，而且这个不设计输入或返回一个函数，为什么？柯里化？好像确实是自带柯里化的诶。 解惑见 用...'))

```coq
Check @doit3times : forall X : Type, (X -> X) -> X -> X.
```

‍

### 过滤器

下面是个更有用的高阶函数，它接受一个元素类型为 **X** 的列表和一个 **X** 的==谓词==（即一个从 **X** 到 **bool** 的函数），然后“过滤”此列表并返回一个新列表， 其中仅包含对该谓词返回 **true** 的元素。

> 类如 python 中的`filter`​

```coq
Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.
```

‍

### 匿名函数

```coq
Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.
```

表达式 **(**​==fun== **n** **⇒** **n** **×** **n**) 可读作“一个给定 **n** 并返回 **n** **×** **n** 的函数。”

‍

### 映射

另一个方便的高阶函数叫做 **map**。

```coq
Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.
```

‍

### 折叠

一个更加强大的高阶函数叫做 **fold**。<u>本函数启发自“</u>​<u>**reduce**</u>​<u>​ 归约” 操作，它是 Google 的 map/reduce 分布式编程框架的核心。</u>

> 参考：[https://cloud.tencent.com/developer/article/1703116](https://hadoop.apache.org/docs/stable/hadoop-mapreduce-client/hadoop-mapreduce-client-core/MapReduceTutorial.html)
>
> https://cloud.tencent.com/developer/article/1703116

```coq
Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.
```

```coq
Check (fold andb) : list bool -> bool -> bool.
Compute (fold andb) [true; true] false.
(* fold andb : list bool -> bool -> bool
	 : list bool -> bool -> bool
	 = false
     : bool
  这也说明了之前我猜测的柯里化是默认的 *)
```

‍

### 用函数构造函数

```coq
Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.
```

实际上，我们已经见过的多参函数也是讲函数作为数据传入的例子。

```coq
Check plus : nat -> nat -> nat.
```

该表达式中的每个 **→** 实际上都是一个类型上的*'二元'*操作符。 该操作符是*'右结合'*的，因此 <u>**plus**</u>​<u>​ 的类型其实是 ​</u>​<u>**nat**</u>​<u>​ ​</u>​<u>**→**</u>​<u>​ ​</u>​<u>**(**</u>​<u>nat ​</u>​<u>**→**</u>​<u>​ ​</u>​<u>**nat**</u>​<u>) 的简写</u>，即，它可以读作“**plus** 是一个单参数函数，它接受一个 **nat** 并返回另一个函数，该函数接受另一个 **nat** 并返回一个 **nat**”。 在上面的例子中，我们总是将 **plus** 一次同时应用到两个参数上。 不过如果我们喜欢，也可以一次只提供一个参数，这叫做*'偏应用（Partial Application）'*。

## 更多练习

​`flod`​ 实现 `length`​ 和 `map`​

```coq
Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y
  (* 将本行替换成 ":= _你的_定义_ ." *) :=
  fold (fun x list_elem_y => f x :: list_elem_y) l [].
```

‍

在 Coq 中，函数 **f** **:** **A** **→** **B** **→** **C** 的类型其实是 **A** **→** **(**B **→** **C**)。 也就是说，如果给 **f** 一个类型为 **A** 的值，它就会给你函数 **f'** **:** **B** **→** **C**。 如果再给 **f'** 一个类型为 **B** 的值，它就会返回一个类型为 **C** 的值。 这为我们提供了 **plus3** 中的那种偏应用能力。 用返回函数的函数处理参数列表的方式被称为*'*​==*柯里化（Currying）*==​*'*， 它是为了纪念逻辑学家 Haskell Curry。

反之，我们也可以将 **A** **→** **B** **→** **C** 解释为 **(**A **×** **B**) **→** **C**。这叫做 *'*​==*反柯里化（Uncurrying）*==​*'*。对于反柯里化的二元函数， 两个参数必须作为序对一次给出，此时它不会偏应用。

我们可以将柯里化定义如下：

```coq
Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).
(** 定义它的反函数 [prod_uncurry] *)
Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z :=
  f (fst p) (snd p).

Check @prod_curry : forall X Y Z : Type, (X * Y -> Z) -> X -> Y -> Z.
Check @prod_uncurry : forall X Y Z : Type, (X -> Y -> Z) -> X * Y -> Z.
```

​#联想#​ *这样看来“序对”就相当于一般编程语言的函数参数输入输出的数据结构*

‍

‍

本练习使用*'邱奇数（Church numerals）'*探讨了另一种定义自然数的方式， 它以数学家 Alonzo Church 命名。我们可以将自然数 **n** 表示为一个函数， 它接受一个函数 **f** 作为参数并返回迭代了 **n** 次的 **f**。

​#TODO#​

‍
