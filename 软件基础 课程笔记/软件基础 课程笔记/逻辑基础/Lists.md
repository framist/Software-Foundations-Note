---
title: Lists
date: 2023-04-16T16:07:02Z
lastmod: 2023-04-16T16:07:25Z
---

# Lists

# 使用结构化的数据    (Lists)

* [数值序对](https://coq-zh.github.io/SF-zh/lf-current/Lists.html#lab65)
* [数值列表](https://coq-zh.github.io/SF-zh/lf-current/Lists.html#lab68)

  * [用列表实现口袋（Bag）](https://coq-zh.github.io/SF-zh/lf-current/Lists.html#lab76)
* [有关列表的论证](https://coq-zh.github.io/SF-zh/lf-current/Lists.html#lab80)

  * [对列表进行归纳](https://coq-zh.github.io/SF-zh/lf-current/Lists.html#lab81)
  * [Search 搜索](https://coq-zh.github.io/SF-zh/lf-current/Lists.html#lab83)
  * [列表练习，第一部分](https://coq-zh.github.io/SF-zh/lf-current/Lists.html#lab84)
  * [列表练习, 第二部分](https://coq-zh.github.io/SF-zh/lf-current/Lists.html#lab87)
* [Options 可选类型](https://coq-zh.github.io/SF-zh/lf-current/Lists.html#lab92)
* [偏映射（Partial Maps）](https://coq-zh.github.io/SF-zh/lf-current/Lists.html#lab95)

## 数值序对

此声明可以读作：“构造数值序对的唯一一种方法，就是将构造子 **pair** 应用到两个 **nat** 类型的参数上。”

```coq
Inductive natprod : Type :=
| pair (n1 n2 : nat).

Notation "( x , y )" := (pair x y).
```

*会不会有符号冲突？注意coq的“函数调用”中的变量分割是空格*

我们还需要向 Coq 展示 **p** 的具体结构，这样 **simpl** 才能对 **fst** 和 **snd** 做模式匹配。通过 **destruct** 可以达到这个目的。

```coq
Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.  destruct p as [n m].  simpl.  reflexivity.  Qed.
```

注意：不同于解构自然数产生两个子目标，**destruct** 在此只产生 一个子目标。这是因为 **natprod** 只有一种构造方法。

‍

‍

## 数值列表

​#联想#​*世界线收束！参照 CS61a 与 SICP 中的列表与链表*

通过推广序对的定义，数值*'列表'*类型可以这样描述： “一个列表要么是空的，要么就是由一个数和另一个列表组成的序对。”

```coq
Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).
```

例如，这是一个三元素列表：

```coq
Definition mylist := cons 1 (cons 2 (cons 3 nil)).
```

```coq
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].
```

*注意右结合 right associativity*

### Repeat、Length、Append、Head 与 Tail

```coq
Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.
Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.
```

​#联想#​ `app`​ *（Append）实际定义了合并列表的函数。在这里coq是使用像数学的形式来定义；一般的函数式语言使用递归来定义；偏底层的语言（例如 C ）直接操作内存中的指针来完成整个定义*

> ​`::`​ ~=元素操作 `cons`​
>
> ​`++`​ ~=列表操作 `app`​

‍

### 用列表实现口袋（Bag）

==**bag**==（或者叫 **multiset** 多重集）类似于集合，只是其中每个元素都能出现不止一次。 口袋的一种可行的表示是列表。

```coq
Fixpoint count (v:nat) (s:bag) : nat :=
  (* 将本行替换成 ":= _你的_定义_ ." *)
  match s with
  | nil => O
  | h :: t => if h =? v
              then S (count v t)
              else count v t
  end.
```

对于以下习题，就有函数式编程的味道了，可以复用函数：

```coq
Definition sum : bag -> bag -> bag :=
  (* 将本行替换成 ":= _你的_定义_ ." *)
  app.
(* 对于参考其他人的解法，有：[  fun l1 l2 => app l1 l2. ] 但是是未学到的*)

Definition member (v:nat) (s:bag) : bool :=
  (* 将本行替换成 ":= _你的_定义_ ." *)
  if 0 <? (count v s)
  then true
  else false.
```

额外的练习：和 **bag** 有关的函数

```coq
Fixpoint remove_one (v:nat) (s:bag) : bag :=
  (* 将本行替换成 ":= _你的_定义_ ." *)
  match s with
  | nil => nil
  | h :: t => if(v =? h) 
              then t 
              else h :: (remove_one v t) 
  end.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  (* 将本行替换成 ":= _你的_定义_ ." *)
  match s with
  | nil => nil
  | h :: t => if(v =? h) 
              then remove_all v t
              else h :: (remove_all v t) 
  end.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  (* 将本行替换成 ":= _你的_定义_ ." *)
  match s1 with
  | nil => true
  | h :: t => if(member h s2) 
              then subset t (remove_one h s2) 
              else false 
  end.
```

## 有关列表的论证

归纳定义的集合中元素的形式 *'只能是'* 构造子对其它项的应用。

```coq
Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.  Qed.
```

### 反转列表

```coq
Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
```

### Search 搜索

我们已经见过很多需要使用之前证明过的结论（例如通过 **rewrite**）来证明的定理了。 但是在引用别的定理时，我们必须事先知道它们的名字。当然，即使是已被证明的定理本身 我们都不能全部记住，更不用提它们的名字了。

Coq 的 ==**Search**== 指令在这时就非常有用了。执行 **Search** **foo** 会让 Coq 显示所有涉及到 **foo** 的定理。例如，去掉下面的注释后， 你会看到一个我们证明过的所有关于 **rev** 的定理的列表：

```coq
Coq < Search rev. 
test_rev2: rev [ ] = [ ]
rev_length: forall l : natlist, length (rev l) = length l
test_rev1: rev [1; 2; 3] = [3; 2; 1]
```

练习

```coq
Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
```

### 列表练习

​#剩余习题未完成#​

‍

## Options 可选类型

假设我们想要写一个返回某个列表中第 **n** 个元素的函数。如果我们为它赋予类型 **nat** **→** **natlist** **→** **nat**，那么当列表太短时我们仍须返回某个数...

*突然发现多输入函数的类型的形式是连蕴含，而且这个不设计输入或返回一个函数，为什么？柯里化？好像确实是自带柯里化的诶。 解惑见 ​*​((20221203205624-buhoh6m '用函数构造函数'))**

一种更好的方式是改变 **nth_bad** 的返回类型，使其包含一个错误值作为可能的结果。 我们将此类型命名为 **natoption**。

```coq
Inductive natoption : Type :=
  | Some (n : nat)
  | None.
```

然后我们可以修改前面 **nth_bad** 的定义，使其在列表太短时返回 **None**， 在列表足够长且 **a** 在 **n** 处时返回 **Some** **a**。我们将这个新函数称为 **nth_error** 来表明它可以产生带错误的结果。

```coq
Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.
```

介绍 Coq 编程语言更多细微特性：比如条件表达式...

Coq 的条件语句和其它语言中的一样，不过加上了一点更为一般化的特性。 由于 **bool** 类型不是内建的，因此 Coq 实际上支持在*'任何'*带有两个构造子的， 归纳定义的类型上使用条件表达式。当断言（guard）求值为 **Inductive** 定义中的第一个构造子时，它被认为是真的；当它被求值到第二个构造子时， 则被认为是假的。

以下函数从 **natoption** 中取出一个 **nat**，在遇到 **None** 时它将返回提供的默认值。

```coq
Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.
```

*这种记法在其他的一些编程语言中也有体现，例如 Rust*

## 偏映射（Partial Maps）

最后演示一下如何在 Coq 中定义基础的数据结构。这是一个简单的 *'偏映射'* 数据类型，它类似于大多数编程语言中的映射或字典数据结构。

首先，我们定义一个新的归纳数据类型 **id** 来用作偏映射的“键”。

```coq
Inductive id : Type :=
  | Id (n : nat).
```

本质上来说，**id** 只是一个数。但通过 **Id** 标签封装自然数来引入新的类型， 能让定义变得更加可读，同时也给了我们更多的灵活性。

我们还需要一个 **id** 的相等关系测试：

```coq
Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.
```

现在我们定义偏映射的类型：

```coq
Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).
```

此声明可以读作：“有两种方式可以构造一个 **partial_map**：用构造子 **empty** 表示一个空的偏映射，或将构造子 **record** 应用到一个键、一个值和一个既有的 **partial_map** 来构造一个带“键-值”映射 的 **partial_map**。”

update 函数在部分映射中覆盖给定的键以取缔原值（如该键尚不存在， 则新建其记录）。

```coq
Definition update (d : partial_map)(x : id) (value : nat)
                  : partial_map :=
  record x value d.
```

最后，**find** 函数按照给定的键搜索一个 **partial_map**。若该键无法找到， 它就返回 **None**；若该键与 **val** 相关联，则返回 **Some** **val**。 若同一个键被映到多个值，**find** 就会返回它遇到的第一个值。

```coq
Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty         => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.
```

*实质上像多元列表，其中一个元不能重复*

‍

​#TODO#​ 一个练习，答案是无穷？

```coq
Inductive baz : Type :=
  | Baz1 (x : baz)
  | Baz2 (y : baz) (b : bool).

(** 有_'多少'_个表达式具备类型 [baz]？（以注释说明。） *)
(* TODO: 无穷个？ *)
```

‍
