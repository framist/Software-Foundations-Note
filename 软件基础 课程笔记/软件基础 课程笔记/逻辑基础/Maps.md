---
title: Maps
date: 2023-04-16T16:12:08Z
lastmod: 2023-04-16T16:13:57Z
---

# Maps

# 全映射与偏映射    (Maps)

* [Coq 标准库](https://coq-zh.github.io/SF-zh/lf-current/Maps.html#lab255)
* [标识符](https://coq-zh.github.io/SF-zh/lf-current/Maps.html#lab256)
* [全映射](https://coq-zh.github.io/SF-zh/lf-current/Maps.html#lab257)
* [偏映射](https://coq-zh.github.io/SF-zh/lf-current/Maps.html#lab265)

*'映射（Map）'*（或*'字典（Dictionary）'*）是一种非常普遍的数据结构， 在编程语言理论中尤甚，而之后的章节中我们会多次用到它。 映射也适合运用之前学过的概念进行研究，包括如何在高阶函数之外构建数据结构 （见 **Basics** 和 **Poly**）以及通过互映来精简证明（见 **IndProp**）。

我们会定义两种映射：在查找的键不存在时，*'全映射'*会返回“默认”元素， 而*'偏映射'*则会返回一个 **option** 来指示成功还是失败。后者根据前者来定义， 它使用 **None** 默认元素。

## Coq 标准库

```coq
From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.
```

标准库的文档见 [https://coq.inria.fr/library/](https://coq.inria.fr/library/)。

## 标识符

首先我们需要键的类型来对映射进行索引。在 **Lists.v** 中， 我们为类似的目的引入了 **id** 类型。而在*'《软件基础》'*后面的部分， 我们会使用 Coq 标准库中的 **string** 类型。

为了比较字符串，我们定义了 **eqb_string** 函数，它在内部使用 Coq 字符串库中的 **string_dec** 函数。

```coq
Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.
```

（函数 **string_dec** 来自于 Coq 的字符串标准库。如果你查看 **string_dec** 的结果类型，就会发现其返回值的类型并不是 **bool**， 而是一个形如`{x = y} + {x <> y}`​的类型，叫做<u>​ ​</u>​<u>**sumbool**</u>​<u>​ 类型， 它可以看做“带有证据的布尔类型”</u>。形式上来说，一个 `{x = y} + {x <> y}`​ 类型的元素要么是 **x** 和 **y** 的相等的证明，要么就是它们不相等的证明， 与一个标签一起来指出具体是哪一个。不过就目前来说，你可以把它当做一个 花哨的 **bool**。）

现在我们需要一些关于字符串相等性的基本性质...

```coq
Theorem eqb_string_refl : forall s : string, true = eqb_string s s.
Proof.
  intros s. unfold eqb_string.
  destruct (string_dec s s) as [Hs_eq | Hs_not_eq].
  - reflexivity.
  - destruct Hs_not_eq. reflexivity.
Qed.

```

两个字符串在 **eqb_string** 的意义上相等，当且仅当它们在 **=** 的意义上相等。因此 **eqb_string** 中反映了 **=**，[IndProp](https://coq-zh.github.io/SF-zh/lf-current/IndProp.html) 一章中<u>讨论了「互映」的意义</u>。

```coq
Theorem eqb_string_true_iff : forall x y : string,
    eqb_string x y = true <-> x = y.
Proof.
   intros x y.
   unfold eqb_string.
   destruct (string_dec x y) as [Hs_eq | Hs_not_eq].
   - rewrite Hs_eq. split. reflexivity. reflexivity.
   - split.
     + intros contra. discriminate contra.
     + intros H. rewrite H in Hs_not_eq. destruct Hs_not_eq. reflexivity.
Qed.

(** 类似地： *)

Theorem eqb_string_false_iff : forall x y : string,
    eqb_string x y = false <-> x <> y.
Proof.
  intros x y. rewrite <- eqb_string_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

(** 以下便于使用的变体只需通过改写就能得出： *)

Theorem false_eqb_string : forall x y : string,
   x <> y -> eqb_string x y = false.
Proof.
  intros x y. rewrite eqb_string_false_iff.
  intros H. apply H. Qed.
```

‍

## 全映射

在本章中，我们的主要任务就是构建一个偏映射的定义，其行为类似于我们之前在 [Lists](https://coq-zh.github.io/SF-zh/lf-current/Lists.html) 一章中看到的那个，再加上伴随其行为的引理。

不过这一次，我们将使用*'函数'*而非“键-值”对的列表来构建映射。 这种表示方法的优点在于它提供了映射更具*'外延性'*的视角， 即以相同方式回应查询的两个映射将被表示为完全相同的东西（即一模一样的函数）， 而非只是“等价”的数据结构。这反过来简化了使用映射的证明。

我们会分两步构建偏映射。首先，我们定义一个*'全映射'*类型， 它在某个映射中查找不存在的键时会返回默认值。

```coq
Definition total_map (A : Type) := string -> A.
(* *定义 total_map 类型* *)
```

直观上来说，一个元素类型为 **A** 的全映射不过就是个根据 **string** 来查找 **A** 的函数。

给定函数 **t_empty** 一个默认元素，它会产生一个空的全映射。 此映射在应用到任何字符串时都会返回默认元素。

```coq
Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).
```

**update** 函数，它和之前一样，接受一个映射 **m**、一个键 **x** 以及一个值 **v**，并返回一个将 **x** 映射到 **v** 的新映射；其它键则与 **m** 中原来的保持一致。此定义是个高阶编程的好例子：**t_update** 接受一个*'函数'* **m** 并产生一个新的函数 **fun** **x'** **⇒** **...**，它的表现与所需的映射一致。

```coq
Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.
```

例如，我们可以构建一个从 **string** 到 **bool** 的映射，其中 **&quot;**foo**&quot;** 和 **&quot;**bar**&quot;** 映射到 **true**，其它键则映射到 **false**，就像这样：

```coq
Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.
```

接下来，我们引入一些新的记法来方便映射的使用。

```coq
(** 首先，我们会使用以下记法，根据一个默认值来创建空的全映射。 *)
Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Example example_empty := (_ !-> false).

(** 然后，我们引入一种方便的记法，通过一些绑定来扩展现有的映射。 *)
Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

(** 前面的 [examplemap] 现在可以定义如下： *)

Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _     !-> false
  ).
```

到这里就完成了全映射的定义。注意我们无需定义 **find** 操作， 因为它不过就是个函数应用！

为了在后面的章节中使用映射，我们需要一些关于其表现的基本事实。

即便你没有进行下面的练习，也要确保透彻地理解以下引理的陈述！

（其中有些证明需要函数的外延性公理，我们在 [Logic](https://coq-zh.github.io/SF-zh/lf-current/Logic.html) 一节中讨论过它）。

​#剩余习题未完成#​

‍

## 偏映射

最后，我们在全映射之上定义*'偏映射'*。元素类型为 **A** 的偏映射不过就是个 元素类型为 **option** **A**，默认元素为 **None** 的全映射。

```coq
Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

(** 我们为偏映射引入类似的记法。 **)
Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

(** 当最后一种情况为空时，我们也可以隐藏它。 *)
Notation "x '|->' v" := (update empty x v)
  (at level 100).

Example examplepmap :=
  ("Church" |-> true ; "Turing" |-> false).
```

现在我们将所有关于全映射的基本引理直接转换成对应的偏映射引理。

```coq
Lemma apply_empty : forall (A : Type) (x : string),
    @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
    (x |-> v ; m) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
    x2 <> x1 ->
    (x2 |-> v ; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H. Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
    (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros A m x v1 v2. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
    m x = Some v ->
    (x |-> v ; m) = m.
Proof.
  intros A m x v H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
    x2 <> x1 ->
    (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros A m x1 x2 v1 v2. unfold update.
  apply t_update_permute.
Qed.

```
