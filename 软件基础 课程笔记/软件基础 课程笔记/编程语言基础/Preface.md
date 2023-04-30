---
title: Preface
date: 2023-04-17T22:15:32Z
lastmod: 2023-04-17T22:16:16Z
---

# Preface

# 前言    (Preface)

* [欢迎](https://coq-zh.github.io/SF-zh/plf-current/Preface.html#lab1)
* [概览](https://coq-zh.github.io/SF-zh/plf-current/Preface.html#lab2)

  * [程序验证](https://coq-zh.github.io/SF-zh/plf-current/Preface.html#lab3)
  * [类型系统](https://coq-zh.github.io/SF-zh/plf-current/Preface.html#lab4)
  * [扩展阅读](https://coq-zh.github.io/SF-zh/plf-current/Preface.html#lab5)
* [实践](https://coq-zh.github.io/SF-zh/plf-current/Preface.html#lab6)

  * [推荐的引用格式](https://coq-zh.github.io/SF-zh/plf-current/Preface.html#lab7)
* [对授课员的要求](https://coq-zh.github.io/SF-zh/plf-current/Preface.html#lab8)
* [鸣谢](https://coq-zh.github.io/SF-zh/plf-current/Preface.html#lab9)

## 欢迎

本书概述了程序和编程语言中数学研究的基本概念，主题涵盖 Coq 证明助理的高级用法、操作语义、霍尔逻辑以及静态类型系统。

## 概览

本书以两个概念作为两条主线来推进：

(1) *'论证具体程序的性质'*的形式化技术 （例如排序函数的性质或满足某些形式化规范的编译器）。

(2) 用*'类型系统'*来确保给定语言编写的*'所有'*程序都行为良好。 （例如良型的 Java 程序不会在运行时被推翻）。

扩展阅读的建议见 [Postscript](https://coq-zh.github.io/SF-zh/plf-current/Postscript.html) 一章。所有引用作品的文献信息见 [Bib](https://coq-zh.github.io/SF-zh/plf-current/Bib.html) 文件。

### 程序验证

本书第一部分介绍了构建可靠的软件（和硬件）时所涉及的两个至关重要的主题： ==证明==​==*'特定程序'*==​==具体性质==的技术，以及==证明==​==*'整个编程语言'*==​==一般性质==的技术。

对于二者而言，首先我们需要将程序表示为数学对象，这样就能准确地讨论它们。 此外还需要基于数学函数或关系来描述它们的行为。为此，我们的主要工具是 ==*'抽象语法（Abstract Syntax）'*==和==*'操作语义（Operational Semantics）'*==， 一种编写抽象解释器来详述编程语言的方法。首先，我们会使用称作「==大步==」 风格的操作语义，适当使用它可产生简单可读的定义。之后，我们会切换到 较为底层的「==小步==」风格，它有助于做出一些有用的区分（例如，不同种类的 不停机程序的行为之间的区别），也适用于更加广泛的语言特性，包括并发。

我们深入探讨的第一个编程语言是 *Imp*，它是一个小型玩具语言， 刻画了常见指令式编程的核心特性：变量、赋值、条件分支和循环。

我们会探究两种不同的方式来论证 Imp 程序。首先，我们会直观理解 「两个 Imp 程序==*'等价（Equivalent）'*==」的含义， 即它们在任何相同的初始内存状态下运行都会表现出相同的行为。 之后「等价」的概念会成为判断==*'元程序（Metaprogram）'*==正确性的标准。 元程序即操纵其它程序（如编译器和优化器）的程序。我们会为 Imp 构建一个简单的优化器并证明它的正确性。

之后，我们发展了一套方法论，用以证明给定 Imp 程序的行为满足某些形式化规范。 我们会介绍==*'霍尔三元组（Hoare Triple）'*==的概念——Imp 程序以前置条件和后置条件进行标注，描述了它们在启动时期望内存中的什么为真， 以及在它们终止时承诺内存中的什么为真。我们还会介绍==*'霍尔逻辑（Hoare Logic）'*==​==​ ​==的推理法则——它是一种专用于方便地组合命令式程序的推理的领域特定逻辑， 其中内建了==“循环不变式（Loop Invariant）”==等概念。

这部分课程旨在让读者领略真实世界中软硬件验证工作所用的关键思想和数学工具。

‍

### 类型系统

另一个重要的主题大约涵盖了本书的后半部分，即==*'类型系统（Type System）'*==， 它是一种在给定的语言中为*'所有的'*程序建立属性的强大工具。 在被称作*'轻量级形式化方法'*的形式化验证技术中，类型系统是最成功的一类， 它也是最完善，最流行的。它们是最合适的推理技术——合适到自动检查器可被内置在 编译器、链接器或程序分析器中，因此它甚至可以被不熟悉底层理论的程序员所应用。 其它的轻量级形式化方法的例子包括硬件和软件模型检查器，约束检查器和运行时监视器技术。

它也与本书的开头形成了完整的闭环：我们在这部分中研究的语言的性质，即 *'简单类型 λ-演算'*，基本上就是 Coq 核心自身模型的简化版！

‍

### 扩展阅读

本书旨在自成一体，不过想要对特定主题进行深入研究的读者，可以在 [Postscript](https://coq-zh.github.io/SF-zh/plf-current/Postscript.html) 一章中找到推荐的扩展阅读。

‍
