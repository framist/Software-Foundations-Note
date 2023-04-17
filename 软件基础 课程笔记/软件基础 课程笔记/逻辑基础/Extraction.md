---
title: Extraction
date: 2023-04-17T14:10:52Z
lastmod: 2023-04-17T16:45:24Z
---

# Extraction

# 从 Coq 中提取 ML    (Extraction)

* [基本的提取方式](https://coq-zh.github.io/SF-zh/lf-current/Extraction.html#lab393)
* [控制提取特定的类型](https://coq-zh.github.io/SF-zh/lf-current/Extraction.html#lab394)
* [一个完整的示例](https://coq-zh.github.io/SF-zh/lf-current/Extraction.html#lab395)
* [讨论](https://coq-zh.github.io/SF-zh/lf-current/Extraction.html#lab396)
* [更进一步](https://coq-zh.github.io/SF-zh/lf-current/Extraction.html#lab397)

> **关于 ML**
>
> **ML**（**M**eta **L**anguage：元语言），是一个[函数式](https://zh.wikipedia.org/wiki/%E5%87%BD%E6%95%B0%E5%BC%8F%E7%BC%96%E7%A8%8B%E8%AF%AD%E8%A8%80 "函数式编程语言")、[指令式](https://zh.wikipedia.org/wiki/%E6%8C%87%E4%BB%A4%E5%BC%8F%E7%BC%96%E7%A8%8B%E8%AF%AD%E8%A8%80 "指令式编程语言")的[通用](https://zh.wikipedia.org/wiki/%E9%80%9A%E7%94%A8%E7%BC%96%E7%A8%8B%E8%AF%AD%E8%A8%80 "通用编程语言")的[编程语言](https://zh.wikipedia.org/wiki/%E7%BC%96%E7%A8%8B%E8%AF%AD%E8%A8%80 "编程语言")，它著称于使用了[多态](https://zh.wikipedia.org/wiki/%E5%A4%9A%E6%80%81_(%E8%AE%A1%E7%AE%97%E6%9C%BA%E7%A7%91%E5%AD%A6)) "多态 (计算机科学)")的[Hindley–Milner类型推论](https://zh.wikipedia.org/wiki/%E7%B1%BB%E5%9E%8B%E6%8E%A8%E8%AE%BA#Hindley%E2%80%93Milner_%E7%B1%BB%E5%9E%8B%E6%8E%A8%E8%AE%BA%E7%AE%97%E6%B3%95 "类型推论")​^[[8]](https://zh.wikipedia.org/wiki/ML%E8%AF%AD%E8%A8%80#cite_note-Milner78-8)^。ML能自动的指定多数[表达式](https://zh.wikipedia.org/w/index.php?title=%E8%A1%A8%E8%BE%BE%E5%BC%8F_(%E8%AE%A1%E7%AE%97%E6%9C%BA%E7%A7%91%E5%AD%A6)&action=edit&redlink=1)的[类型](https://zh.wikipedia.org/wiki/%E6%95%B0%E6%8D%AE%E7%B1%BB%E5%9E%8B "数据类型")，不要求显式的类型标注，而且能够确保类型安全，已经正式证明了有良好类型的ML程序不会导致运行时间类型错误^[[8]](https://zh.wikipedia.org/wiki/ML%E8%AF%AD%E8%A8%80#cite_note-Milner78-8)^。
>
> **关于 OCaml**
>
> 综上所述，ocaml适合写高性能，单线程，专门性强，结构复杂，正确度高的软件
>
> 现在一般用于编译器，程序分析，金融交易，虚拟机等方面
>
> rust最初编译器就是OCaml写的、后面才自举的

‍

## 基本的提取方式

对于用 Coq 编写的代码而言，从中提取高效程序的最简方式是十分直白的。

首先我们需要指定提取的目标语言。可选的语言有三种：<u>提取机制最为成熟的 OCaml</u>，<u>提取结果大都可以直接使用的 Haskell</u>，<u>以及提取机制有些过时的 Scheme</u>。

```coq
Require Coq.extraction.Extraction.
Extraction Language OCaml.
```

现在我们将待提取的定义加载到 Coq 环境中。你可以直接写出定义， 也可以从其它模块中加载。

```coq
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From LF Require Import ImpCEvalFun.
```

最后，我们来指定需要提取的定义，以及用于保存提取结果的文件名。

```coq
Extraction "imp1.ml" ceval_step.
```

Coq 在处理此指令时会生成一个名为 **imp1.ml** 的文件，其中包含了提取后的 **ceval_step** 以及所有递归依赖的文件。编译本章对应的 **.**v 文件，然后看看生成的 **imp1.ml** 吧！

```ocaml
type bool =
| True
| False

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type sumbool =
| Left
| Right

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val mul : nat -> nat -> nat **)

let rec mul n m =
  match n with
  | O -> O
  | S p -> add m (mul p m)

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

(** val bool_dec : bool -> bool -> sumbool **)

let bool_dec b1 b2 =
  match b1 with
  | True -> (match b2 with
             | True -> Left
             | False -> Right)
  | False -> (match b2 with
              | True -> Right
              | False -> Left)

module Nat =
 struct
  (** val eqb : nat -> nat -> bool **)

  let rec eqb n m =
    match n with
    | O -> (match m with
            | O -> True
            | S _ -> False)
    | S n' -> (match m with
               | O -> False
               | S m' -> eqb n' m')

  (** val leb : nat -> nat -> bool **)

  let rec leb n m =
    match n with
    | O -> True
    | S n' -> (match m with
               | O -> False
               | S m' -> leb n' m')
 end

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val ascii_dec : ascii -> ascii -> sumbool **)

let ascii_dec a b =
  let Ascii (b0, b1, b2, b3, b4, b5, b6, b7) = a in
  let Ascii (b8, b9, b10, b11, b12, b13, b14, b15) = b in
  (match bool_dec b0 b8 with
   | Left ->
     (match bool_dec b1 b9 with
      | Left ->
        (match bool_dec b2 b10 with
         | Left ->
           (match bool_dec b3 b11 with
            | Left ->
              (match bool_dec b4 b12 with
               | Left ->
                 (match bool_dec b5 b13 with
                  | Left -> (match bool_dec b6 b14 with
                             | Left -> bool_dec b7 b15
                             | Right -> Right)
                  | Right -> Right)
               | Right -> Right)
            | Right -> Right)
         | Right -> Right)
      | Right -> Right)
   | Right -> Right)

type string =
| EmptyString
| String of ascii * string

(** val string_dec : string -> string -> sumbool **)

let rec string_dec s x =
  match s with
  | EmptyString -> (match x with
                    | EmptyString -> Left
                    | String (_, _) -> Right)
  | String (a, s0) ->
    (match x with
     | EmptyString -> Right
     | String (a0, s1) -> (match ascii_dec a a0 with
                           | Left -> string_dec s0 s1
                           | Right -> Right))

(** val eqb_string : string -> string -> bool **)

let eqb_string x y =
  match string_dec x y with
  | Left -> True
  | Right -> False

type 'a total_map = string -> 'a

(** val t_update : 'a1 total_map -> string -> 'a1 -> string -> 'a1 **)

let t_update m x v x' =
  match eqb_string x x' with
  | True -> v
  | False -> m x'

type state = nat total_map

type aexp =
| ANum of nat
| AId of string
| APlus of aexp * aexp
| AMinus of aexp * aexp
| AMult of aexp * aexp

type bexp =
| BTrue
| BFalse
| BEq of aexp * aexp
| BLe of aexp * aexp
| BNot of bexp
| BAnd of bexp * bexp

(** val aeval : state -> aexp -> nat **)

let rec aeval st = function
| ANum n -> n
| AId x -> st x
| APlus (a1, a2) -> add (aeval st a1) (aeval st a2)
| AMinus (a1, a2) -> sub (aeval st a1) (aeval st a2)
| AMult (a1, a2) -> mul (aeval st a1) (aeval st a2)

(** val beval : state -> bexp -> bool **)

let rec beval st = function
| BTrue -> True
| BFalse -> False
| BEq (a1, a2) -> Nat.eqb (aeval st a1) (aeval st a2)
| BLe (a1, a2) -> Nat.leb (aeval st a1) (aeval st a2)
| BNot b1 -> negb (beval st b1)
| BAnd (b1, b2) -> (match beval st b1 with
                    | True -> beval st b2
                    | False -> False)

type com =
| CSkip
| CAss of string * aexp
| CSeq of com * com
| CIf of bexp * com * com
| CWhile of bexp * com

(** val ceval_step : state -> com -> nat -> state option **)

let rec ceval_step st c = function
| O -> None
| S i' ->
  (match c with
   | CSkip -> Some st
   | CAss (l, a1) -> Some (t_update st l (aeval st a1))
   | CSeq (c1, c2) -> (match ceval_step st c1 i' with
                       | Some st' -> ceval_step st' c2 i'
                       | None -> None)
   | CIf (b, c1, c2) -> (match beval st b with
                         | True -> ceval_step st c1 i'
                         | False -> ceval_step st c2 i')
   | CWhile (b1, c1) ->
     (match beval st b1 with
      | True -> (match ceval_step st c1 i' with
                 | Some st' -> ceval_step st' c i'
                 | None -> None)
      | False -> Some st))

```

*同样。也可以提取另外两种语言，略*

‍

## 控制提取特定的类型

我们可以让 Coq 将具体的 **Inductive** 定义提取为特定的 OCaml 类型。 对于每一个定义，我们都要指明：

* 该 Coq 类型应当如何用 OCaml 来表示
* 该类型的构造子应如何转换为目标语言中对应的标识符。

```ocaml
Extract Inductive bool => "bool" [ "true" "false" ].
```

对于非枚举类型（即构造器接受参数的类型），我们需要给出一个 OCaml 表达式来作为该类型元素上的“递归器”。（想想==丘奇数==。）

（译注：在这一部分，读者可以在为 **nat** 指定对应的类型后使用 **Extraction** **plus** 来得到自然数加法的提取结果，以此加深对“递归器”的理解。）

```ocaml
Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n ->
      if n=0 then zero () else succ (n-1))".
```

我们也可以将定义的常量提取为具体的 OCaml 项或者操作符。

```ocaml
Extract Constant plus => "( + )".
Extract Constant mult => "( * )".
Extract Constant eqb => "( = )".
```

注意：保证提取结果的合理性是*'你的责任'*。例如，以下指定可能十分自然：

```ocaml
      Extract Constant minus => "( - )".
```

但是这样做会引起严重的混乱。（思考一下。为什么会这样呢？：*不闭合？*）

```ocaml
Extraction "imp2.ml" ceval_step.
```

检查一下生成的 **imp2.ml** 文件，留意一下此次的提取结果与 **imp1.ml** 有何不同。

```diff
type bool =                                                   <
| True                                                        <
| False                                                       <
                                                              <
(** val negb : bool -> bool **)                                 (** val negb : bool -> bool **)

let negb = function                                             let negb = function
| True -> False                                               | | true -> false
| False -> True                                               | | false -> true
                                                              <
type nat =                                                    <
| O                                                           <
| S of nat                                                    <

type 'a option =                                                type 'a option =
| Some of 'a                                                    | Some of 'a
| None                                                          | None

type sumbool =                                                  type sumbool =
| Left                                                          | Left
| Right                                                         | Right

(** val add : nat -> nat -> nat **)                           | (** val add : int -> int -> int **)

let rec add n m =                                             | let rec add = ( + )
  match n with                                                <
  | O -> m                                                    <
  | S p -> S (add p m)                                        <

(** val mul : nat -> nat -> nat **)                           | (** val mul : int -> int -> int **)

let rec mul n m =                                             | let rec mul = ( * )
  match n with                                                <
  | O -> O                                                    <
  | S p -> add m (mul p m)                                    <

(** val sub : nat -> nat -> nat **)                           | (** val sub : int -> int -> int **)

let rec sub n m =                                               let rec sub n m =
  match n with                                                |   (fun zero succ n ->
  | O -> n                                                    |       if n=0 then zero () else succ (n-1))
  | S k -> (match m with                                      |     (fun _ -> n)
            | O -> n                                          |     (fun k -> (fun zero succ n ->
            | S l -> sub k l)                                 |       if n=0 then zero () else succ (n-1))
                                                              >                 (fun _ -> n)
                                                              >                 (fun l -> sub k l)
                                                              >                 m)
                                                              >     n

(** val bool_dec : bool -> bool -> sumbool **)                  (** val bool_dec : bool -> bool -> sumbool **)

let bool_dec b1 b2 =                                            let bool_dec b1 b2 =
  match b1 with                                               |   if b1 then if b2 then Left else Right else if b2 then Right
  | True -> (match b2 with                                    <
             | True -> Left                                   <
             | False -> Right)                                <
  | False -> (match b2 with                                   <
              | True -> Right                                 <
              | False -> Left)                                <

module Nat =                                                    module Nat =
 struct                                                          struct
  (** val eqb : nat -> nat -> bool **)                        |   (** val eqb : int -> int -> bool **)

  let rec eqb n m =                                               let rec eqb n m =
    match n with                                              |     (fun zero succ n ->
    | O -> (match m with                                      |       if n=0 then zero () else succ (n-1))
            | O -> True                                       |       (fun _ ->
            | S _ -> False)                                   |       (fun zero succ n ->
    | S n' -> (match m with                                   |       if n=0 then zero () else succ (n-1))
               | O -> False                                   |         (fun _ -> true)
               | S m' -> eqb n' m')                           |         (fun _ -> false)
                                                              >         m)
                                                              >       (fun n' ->
                                                              >       (fun zero succ n ->
                                                              >       if n=0 then zero () else succ (n-1))
                                                              >         (fun _ -> false)
                                                              >         (fun m' -> eqb n' m')
                                                              >         m)
                                                              >       n

  (** val leb : nat -> nat -> bool **)                        |   (** val leb : int -> int -> bool **)

  let rec leb n m =                                               let rec leb n m =
    match n with                                              |     (fun zero succ n ->
    | O -> True                                               |       if n=0 then zero () else succ (n-1))
    | S n' -> (match m with                                   |       (fun _ -> true)
               | O -> False                                   |       (fun n' ->
               | S m' -> leb n' m')                           |       (fun zero succ n ->
                                                              >       if n=0 then zero () else succ (n-1))
                                                              >         (fun _ -> false)
                                                              >         (fun m' -> leb n' m')
                                                              >         m)
                                                              >       n
 end                                                             end
...
```

‍

## 一个完整的示例

为了使用提取的求值器运行 Imp 程序，我们还需要一个小巧的驱动程序 来调用求值器并输出求值结果。

为简单起见，我们只取最终状态下前四个存储空间中的内容作为程序的结果。 （译注：这里的存储空间指作为状态的 **map**。）

为了更方便地输入例子，我们将会从 **ImpParser** 模块中提取出语法解析器。 首先需要正确建立 Coq 中的字符串与 OCaml 中字符列表的对应关系。

```coq
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
```

我们还需要翻译另一种布尔值：

```coq
Extract Inductive sumbool => "bool" ["true" "false"].
```

提取指令是相同的。

```coq
From LF Require Import Imp.
From LF Require Import ImpParser.

From LF Require Import Maps.
Extraction "imp3.ml" empty_st ceval_step parse.
```

现在我们来运行一下生成的 Imp 求值器。首先你应该阅览一下 **impdriver.ml**（这并非从某个 Coq 源码提取而来，它是手写的。）

然后用下面的指令将求值器与驱动程序一同编译成可执行文件：

```bash
ocamlc -w -20 -w -26 -o impdriver imp.mli imp.ml impdriver.ml
        ./impdriver
```

​#TODO#​ 实际实验没成功：

```
x:=1 ;; y:=2
Syntax error

true
Syntax error

SKIP
Result: [0 0 0 0 ...]

SKIP;;SKIP
Result: [0 0 0 0 ...]

WHILE true DO SKIP END
Still running after 1000 steps

x:=3
Syntax error

x:=3;; WHILE 0<=x DO SKIP END
Syntax error

x:=3;; WHILE 1<=x DO y:=y+1;; x:=x-1 END
Syntax error
```

## 讨论

由于我们证明了 **ceval_step** 函数的行为在适当的意义上与 **ceval** 关系一致，因此提取出的程序可视作*'已验证的'* Imp 解释器。 当然，我们使用的语法分析器并未经过验证，因为我们并未对它进行任何证明！

‍

## 更进一步

有关提取的更多详情见*'软件基础'*第三卷*'已验证的函数式算法'*中的 Extract 一章。
