---
title: IndPrinciples
date: 2023-04-16T16:14:51Z
lastmod: 2023-04-16T16:16:28Z
---

# IndPrinciples

# 归纳法则    (IndPrinciples)

* [基础](https://coq-zh.github.io/SF-zh/lf-current/IndPrinciples.html#lab282)
* [多态](https://coq-zh.github.io/SF-zh/lf-current/IndPrinciples.html#lab288)
* [归纳假设](https://coq-zh.github.io/SF-zh/lf-current/IndPrinciples.html#lab293)
* [深入 ](https://coq-zh.github.io/SF-zh/lf-current/IndPrinciples.html#lab294)​**[induction](https://coq-zh.github.io/SF-zh/lf-current/IndPrinciples.html#lab294)**​[ 策略](https://coq-zh.github.io/SF-zh/lf-current/IndPrinciples.html#lab294)
* [Prop 中的归纳法则](https://coq-zh.github.io/SF-zh/lf-current/IndPrinciples.html#lab296)
* [形式化 vs. 非形式化的归纳证明](https://coq-zh.github.io/SF-zh/lf-current/IndPrinciples.html#lab297)

  * [对归纳定义的集合进行归纳](https://coq-zh.github.io/SF-zh/lf-current/IndPrinciples.html#lab298)
  * [对归纳定义的命题进行归纳](https://coq-zh.github.io/SF-zh/lf-current/IndPrinciples.html#lab299)
* [Explicit Proof Objects for Induction (Optional)](https://coq-zh.github.io/SF-zh/lf-current/IndPrinciples.html#lab300)
* [The Coq Trusted Computing Base](https://coq-zh.github.io/SF-zh/lf-current/IndPrinciples.html#lab301)

​#TODO#​*一点都没有学*

## 基础

每当我们使用 **Inductive** 来声明数据类型时，Coq 就会自动为该类型生成 *'归纳法则'*。这个归纳法则也是定理：如果 **t** 是归纳定义的，那么对应的 归纳法则被称作 **t_**​==**ind**==。这是自然数的归纳法则：

```coq
nat_ind
	 : forall P : nat -> Prop,
       P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
```

‍

## 多态

‍

## 归纳假设

‍

## 深入 induction 策略

‍

## Prop 中的归纳法则

‍

## 形式化 vs. 非形式化的归纳证明

### 对归纳定义的集合进行归纳

### 对归纳定义的命题进行归纳

‍

## Explicit Proof Objects for Induction (Optional)

‍

## Coq 可信计算基 (The Coq Trusted Computing Base)

任何自动化证明助手都会遇到一个问题，即“为什么要信任它？”：如果实现中存在错误导致其所有推理都成为可疑的，该怎么办？

虽然无法完全消除这些担忧，但 Coq 基于 Curry-Howard 对应关系的事实使其具有坚实的基础。因为命题只是类型，证明只是项，检查所声称的命题的证明是否有效只是对术语进行类型检查。类型检查器是相对较小和直接的程序，因此 Coq 的“可信计算基”——我们必须相信其正确运行的代码部分也很小。

类型检查器必须做什么？其主要工作是确保在每个函数应用中，预期的实际参数类型匹配，匹配表达式的分支是归纳类型的构造器模式，并且匹配的所有分支返回相同的类型等等。

‍

有一些额外的细节：

* 由于 Coq 类型本身也可以是表达式，因此在比较它们之前，检查器必须将它们规范化（使用计算规则）。
* 检查器必须确保`match`​是*全面的*。也就是说，对于每个可能的构造函数，都必须有一个分支。要了解原因，请考虑以下所谓的证明对象：

  ```coq
    Definition or_bogus : forall P Q, P \/ Q -> P :=
      fun (P Q : Prop) (A : P \/ Q) =>
         match A with
         | or_introl H => H
         end.
  ```

  这里所有的类型都匹配正确，但是`match`​只考虑了 `or`​ 的可能构造函数之一。Coq 的全面性检查将拒绝此定义。
* 检查器必须确保每个 `fix`​ 表达式都终止。它使用语法检查来执行此操作，以确保每个递归调用都在原始参数的子表达式上。要了解为什么这很重要，请考虑以下所谓的证明：

  ```coq
    Definition nat_false : forall (n:nat), False :=
       fix f (n:nat) : False := f n.
  ```

  同样，这也是完全符合类型的，但是（幸运的是）Coq 将拒绝它。

请注意，Coq 的健全性仅取决于此类型检查引擎的正确性，而不取决于策略机制。如果策略实现中存在错误（这确实会发生！），那么该策略可能会构造出一个无效的证明项。但是当您键入Qed时，Coq会从头开始检查该术语的有效性。只有通过类型检查器的证明才能在进一步的证明开发中使用。

‍
