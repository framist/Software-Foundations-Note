---
title: ProofObjects
date: 2023-04-16T16:14:06Z
lastmod: 2023-04-16T16:14:28Z
---

# ProofObjects

# 柯里-霍华德对应    (ProofObjects)

* [证明脚本](https://coq-zh.github.io/SF-zh/lf-current/ProofObjects.html#lab266)
* [量词，蕴含式，函数](https://coq-zh.github.io/SF-zh/lf-current/ProofObjects.html#lab268)
* [使用策略编程](https://coq-zh.github.io/SF-zh/lf-current/ProofObjects.html#lab269)
* [逻辑联结词作为归纳类型](https://coq-zh.github.io/SF-zh/lf-current/ProofObjects.html#lab270)

  * [合取](https://coq-zh.github.io/SF-zh/lf-current/ProofObjects.html#lab271)
  * [析取](https://coq-zh.github.io/SF-zh/lf-current/ProofObjects.html#lab273)
  * [存在量化](https://coq-zh.github.io/SF-zh/lf-current/ProofObjects.html#lab275)
  * [True和False](https://coq-zh.github.io/SF-zh/lf-current/ProofObjects.html#lab277)
* [相等关系](https://coq-zh.github.io/SF-zh/lf-current/ProofObjects.html#lab278)

  * [再论反演](https://coq-zh.github.io/SF-zh/lf-current/ProofObjects.html#lab281)

*'算法是证明的计算性内容。' --Robert Harper*

前文已讨论过 Coq 既可以用 **nat**、**list** 等归纳类型及其函数*'编程'*，又可以用归纳命题（如 **ev**）、蕴含式、全称量词等工具*'证明'*程序的性质。我们一直 以来区别对待此两种用法，在很多情况下确实可以这样。但也有迹象表明在 Coq 中编 程与证明紧密相关。例如，<u>关键字 ​</u>​<u>**Inductive**</u>​<u>​ 同时用于声明数据类型和命题</u>，<u>以及 ​</u>​<u>**→**</u>​<u>​ 同时用于描述函数类型和逻辑蕴含式</u>。这可并不是语法上的巧合！事实上，在 Coq 里面程序和证明几乎就是同一件事情。这一章我们会学习背后的原理。

我们已经知道这个基础的思想：<u>在Coq里面，可证明性表现为拥有具体的</u>​<u>*'证据'*</u>​<u>。 为基本命题构造证明，实则以树状结构表示其证据</u>。

对于形如 **A** **→** **B** 的蕴含式，<u>其证明为证据</u>​<u>*'转化装置（transformer）'*</u>​<u>，可将任何证明 ​</u>​<u>**A**</u>​<u>​ 的依据转化为 ​</u>​<u>**B**</u>​<u>​ 的证据。所以从根本上来讲，证明仅仅就是操纵证据的程序</u>。

试问：如果是证据是数据，那么命题本身是什么？

答曰：类型也！

回顾一下 **ev** 这个性质的形式化定义。

```coq
Print ev.
(* ==>
  Inductive ev : nat -> Prop :=
    | ev_0 : ev 0
    | ev_SS : forall n, ev n -> ev (S (S n)).
*)

```

**ev** **0** 的证明”而非“**ev_0** 的类型为 **ev** **0**”。

<u>此处 ​</u>​<u>**:**</u>​<u>​ 既在类型层面表达“具有……类型”，又在命题层面表示“是……的证明”。 这种双关称为</u>​<u>*'柯里-霍华德同构（Curry-Howard correspondence）'*</u>​<u>。</u> 它指出了逻辑与计算之间的深层联系：

$$
命题 \sim 类型\\
证明 \sim 数据值
$$

[[Wadler 2015]](https://coq-zh.github.io/SF-zh/lf-current/Bib.html#Wadler-2015) 里有简单的历史和最新的详细介绍可供参考。

该同构启发很多看问题的新方法。首先，对 **ev_SS** 构造子的理解变得更加自然：

```coq
Check ev_SS
  : forall n,
    ev n ->
    ev (S (S n)).
```

可以将其读作“**ev_SS** 构造子接受两个参数——数字 **n** 以及命题 **ev** **n** 的证明——并产生 **ev (S (S n))** 的证明。”

现在让我们回顾一下之前有关 **ev** 的一个证明。

```coq
Theorem ev_4 : ev 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0. Qed.
```

就像是处理普通的数据值和函数一样，我们可以使用 **Print** 指令来查看 这个证明脚本所产生的*'证据对象 (proof object)'*

```coq
Print ev_4.
(* ===> ev_4 = ev_SS 2 (ev_SS 0 ev_0)
     : ev 4  *)
```

实际上，我们也可以不借助脚本*'直接'*写出表达式作为证明。

```coq
Check (ev_SS 2 (ev_SS 0 ev_0))
  : ev 4.
```

表达式 **ev_SS 2 (ev_SS 0 ev_0)** 可视为向构造子 **ev_SS** 传入参数 2 和 0 等参数，以及对应的 **ev** **2** 与 **ev** **0** 之依据所构造的证明。或言之，视 **ev_SS** 为“构造证明”之原语，需要给定一个数字，并进一步提供该数为偶数之依据以构造证明。 其类型表明了它的功能：

​`forall n, ev n -> ev (S (S n)),`​

类似地，多态类型 **∀** **X**, **list** **X** 表明可以将 **nil** 视为从某类型到由该类型元素组成的空列表的函数。

我们在 [Logic](https://coq-zh.github.io/SF-zh/lf-current/Logic.html) 这一章中已经了解到，我们可以使用函数应用 的语法来实例化引理中的全称量化变量，也可以使用该语法提供引理所要求 的假设。例如：

```coq
Theorem ev_4': ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.
```

‍

### 证明脚本

我们一直在讨论的*'证明对象 (Proof Objects)'*是Coq如何运作的核心。 当Coq执行一个证明脚本的时候，在内部，Coq逐渐构造出一个证明对象—— 一个类型是想要证明的命题的项。在 **Proof** 和 **Qed** 之间的策略告诉 Coq如何构造该项。为了了解这个过程是如何进行的，在下面的策略证明里， 我们在多个地方使用 **Show** **Proof** 指令来显示当前证明树的状态。

```coq
Theorem ev_4'' : ev 4.
Proof.
  Show Proof.   (* ?Goal *)
  apply ev_SS.
  Show Proof.   (* (ev_SS 2 ?Goal) *)
  apply ev_SS.
  Show Proof.   (* (ev_SS 2 (ev_SS 0 ?Goal)) *)
  apply ev_0.
  Show Proof.   (* (ev_SS 2 (ev_SS 0 ev_0)) *)
Qed.
```

在任意的给定时刻，Coq已经构造了一个包含一个“洞(hole)”（即 **?**Goal ）的项，并且Coq知道该洞需要什么类型的证据来填补。

每一个洞对应一个子目标。当没有子目标时，代表证明已经完成。此时，<u>我们构造的证明将会被存储在全局环境中，其名字就是在 ​</u>​<u>**Theorem**</u>​<u>​ 中给定的名字</u>

策略证明非常有用且方便，但是它们并不是必要的：原则上，我们总是能够手动构造想要的证据，如下所示。<u>此处我们可以通过 ​</u>​<u>**Definition**</u>​<u>​ （而非 ​</u>​<u>**Theorem**</u>​<u>）来直接给这个证据一个全局名称。</u>

```coq
Definition ev_4''' : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).
(* 如果给出的定义（证明）有误，报错是类型不匹配。 例如：
Error: The term "ev_SS 2 (ev_SS 0 ev_0)" has type "ev 4"
while it is expected to have type "ev 8".
*)
```

所有这些构造证明的不同方式，对应的存储在全局环境中的证明是完全一样的。

```coq
Print ev_4.
(* ===> ev_4    =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4'.
(* ===> ev_4'   =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4''.
(* ===> ev_4''  =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4'''.
(* ===> ev_4''' =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
```

写出对应 **ev** **8** 的策略证明和证明对象。

```coq
Theorem ev_8 : ev 8.
Proof.
  (* 请在此处解答 *) 
  apply ev_SS.
  apply ev_SS.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Definition ev_8' : ev 8
  (* 将本行替换成 ":= _你的_定义_ ." *) 
  := ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0))).
```

‍

### 量词，蕴含式，函数

> 复习：
>
> 构造子：
>
> ```coq
> Inductive rgb : Type :=
>   | red
>   | green
>   | blue.
> ```
>
> 蕴含式：
>
> 函数：
>
> ```coq
> Definition next_weekday (d:day) : day :=
>   match d with
>   | monday    => tuesday
>   | tuesday   => wednesday
>   end.
> ```

在Coq的计算世界里（即所有的数据结构和程序存在的地方），有两种值的类型中拥有箭头：一种是***'构造子(Constructor)'***，它通过归纳地定义数据类型 引入，另一种是***'函数(Function)'***。

类似地，在Coq的逻辑世界里（即我们运用证明的地方），有两种方式来给与蕴含式需要的证据：构造子，通过归纳地定义命题引入，和...函数！

例如，考虑下列陈述：

```coq
Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.
```

对应 **ev_plus4** 的证明对象是什么？

我们在寻找一个*'类型(Type)'*是 **∀** **n**, **ev** **n** **→** **ev** **(4** **+** **n**) 的表达式——也就是说，<u>一个接受两个参数（一个数字和一个证据）并返回一个证据的 ​</u>​<u>*'函数(Function)'*</u>​<u>!</u>

它的证据对象：

```coq
Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
  fun (n : nat) => fun (H : ev n) =>
    ev_SS (S (S n)) (ev_SS n H).
```

回顾 **fun** **n** **⇒** **blah** 意味着“一个函数，给定 **n**，产生 **blah**”， 并且Coq认为 **4** **+** **n** 和 **S (S (S (S n))) ​**是同义词，所以另一种写出 这个定义的方式是：

```coq
Definition ev_plus4'' (n : nat) (H : ev n)
                    : ev (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).

Check ev_plus4''
  : forall n : nat,
    ev n ->
    ev (4 + n).
```

当我们将 **ev_plus4** 证明的命题视为一个函数类型时，我们可以发现一个 有趣的现象：第二个参数的类型，**ev** **n**，依赖于第一个参数 **n** 的*'值'*。

虽然这样的==*'依赖类型 (Dependent type)'*==在传统的编程语言中并不存在， 但是它们对于编程来说有时候非常有用。最近它们在函数式编程社区里的活 跃很好地表明了这一点。

<u>注意到蕴含式（</u>​<u>**→**</u>​<u>）和量化（</u>​<u>**∀**</u>​<u>）都表示证据上的函数。事实上，他们 是同一个东西</u>：当我们使用**∀**时没有依赖，就可以简写为当**→**。即，我 们没有必要给与箭头左边的类型一个名字：  
**​           ∀ (x:nat), nat
        = ∀ (_:nat), nat
        = nat → nat**

例如，考虑下列命题：

```coq
Definition ev_plus2 : Prop :=
  forall n, forall (E : ev n), ev (n + 2).
```

这个命题的一个证明项会是一个拥有两个参数的函数：一个数字**n** 和一个表明**n**是偶数的证据**E**。但是对于这个证据来说，名字**E**并没有 在**ev_plus2**剩余的陈述里面被使用，所以还专门为它取一个名字并没有意义。因此我们可以使用虚拟标志符**_**来替换真实的名字：

```coq
Definition ev_plus2' : Prop :=
  forall n, forall (_ : ev n), ev (n + 2).
```

或者，等同地，我们可以使用更加熟悉的记号：

```coq
Definition ev_plus2'' : Prop :=
  forall n, ev n -> ev (n + 2).
```

<u>总的来说，&quot;</u>​<u>**P**</u>​<u>​ ​</u>​<u>**→**</u>​<u>​ ​</u>​<u>**Q**</u>​<u>&quot;只是 &quot;</u>​<u>**∀ (_:P), Q**</u>​<u>&quot;的语法糖。</u>

‍

> https://zh.wikipedia.org/wiki/%E4%BE%9D%E8%B5%96%E7%B1%BB%E5%9E%8B
>
> 在[计算机科学](https://zh.wikipedia.org/wiki/%E8%AE%A1%E7%AE%97%E6%9C%BA%E7%A7%91%E5%AD%A6 "计算机科学")和[逻辑](https://zh.wikipedia.org/wiki/%E9%80%BB%E8%BE%91 "逻辑")中，**依赖类型**（或**依存类型**，**dependent type**）是指依赖于值的[类型](https://zh.wikipedia.org/wiki/%E7%B1%BB%E5%9E%8B "类型")，其理论同时包含了[数学基础](https://zh.wikipedia.org/wiki/%E6%95%B0%E5%AD%A6%E5%9F%BA%E7%A1%80 "数学基础")中的[类型论](https://zh.wikipedia.org/wiki/%E7%B1%BB%E5%9E%8B%E8%AE%BA "类型论")和计算机编程中用以减少[程序错误](https://zh.wikipedia.org/wiki/%E7%A8%8B%E5%BA%8F%E9%94%99%E8%AF%AF "程序错误")的[类型系统](https://zh.wikipedia.org/wiki/%E7%B1%BB%E5%9E%8B%E7%B3%BB%E7%BB%9F "类型系统")两方面。在 [Per Martin-Löf](https://zh.wikipedia.org/wiki/Per_Martin-L%C3%B6f "Per Martin-Löf") 的[直觉类型论](https://zh.wikipedia.org/wiki/%E7%9B%B4%E8%A7%89%E7%B1%BB%E5%9E%8B%E8%AE%BA "直觉类型论")中，依赖类型可对应于[谓词逻辑](https://zh.wikipedia.org/wiki/%E8%B0%93%E8%AF%8D%E9%80%BB%E8%BE%91 "谓词逻辑")中的[全称量词](https://zh.wikipedia.org/wiki/%E5%85%A8%E7%A7%B0%E9%87%8F%E8%AF%8D "全称量词")和[存在量词](https://zh.wikipedia.org/wiki/%E5%AD%98%E5%9C%A8%E9%87%8F%E8%AF%8D "存在量词")；在依赖类型[函数式编程语言](https://zh.wikipedia.org/wiki/%E5%87%BD%E6%95%B0%E5%BC%8F%E7%BC%96%E7%A8%8B%E8%AF%AD%E8%A8%80 "函数式编程语言")如 [ATS](https://zh.wikipedia.org/wiki/%E8%87%AA%E5%8B%95%E5%88%97%E8%BB%8A%E5%81%9C%E6%AD%A2%E8%A3%9D%E7%BD%AE "自动列车停止设备")、[Agda](https://zh.wikipedia.org/wiki/Agda "Agda")、[Dependent ML](https://zh.wikipedia.org/w/index.php?title=Dependent_ML&action=edit&redlink=1 "Dependent ML（页面不存在）")、[Epigram](https://zh.wikipedia.org/w/index.php?title=Epigram&action=edit&redlink=1 "Epigram（页面不存在）")、[F*](https://zh.wikipedia.org/wiki/F* "F*") 和 [Idris](https://zh.wikipedia.org/wiki/Idris "Idris") 中，依赖类型系统通过极其丰富的类型表达能力使得程序规范得以借助类型的形式被检查，从而有效减少程序错误。
>
> 依赖类型的两个常见实例是**依赖函数类型**（又称**依赖乘积类型**、**Π-类型**）和**依赖值对类型**（又称**依赖总和类型**、**Σ-类型**）。一个依赖类型函数的返回值类型可以依赖于某个参数的具体值，而非仅仅参数的类型，例如，一个输入参数为整型值n的函数可能返回一个长度为n的数组；一个依赖类型值对中的第二个值可以依赖于第一个值，例如，依赖类型可表示这样的类型：它由一对整数组成，其中的第二个数总是大于第一个数。
>
> 依赖类型增加了类型系统的复杂度。由于确定两个依赖于值的类型的等价性需要涉及具体的计算，若允许在依赖类型中使用任意值的话，其[类型检查](https://zh.wikipedia.org/wiki/%E7%B1%BB%E5%9E%8B%E6%A3%80%E6%9F%A5 "类型检查")将会成为[不可判定问题](https://zh.wikipedia.org/wiki/%E4%B8%8D%E5%8F%AF%E5%88%A4%E5%AE%9A%E9%97%AE%E9%A2%98%E5%88%97%E8%A1%A8 "不可判定问题列表")；换言之，无法确保程序的类型检查一定会停机。
>
> 由于[Curry-Howard同构](https://zh.wikipedia.org/wiki/Curry-Howard%E5%90%8C%E6%9E%84 "Curry-Howard同构")揭示了程序语言的[类型论](https://zh.wikipedia.org/wiki/%E7%B1%BB%E5%9E%8B%E8%AE%BA "类型论")与证明论的[直觉逻辑](https://zh.wikipedia.org/wiki/%E7%9B%B4%E8%A7%89%E9%80%BB%E8%BE%91 "直觉逻辑")之间的紧密关联性，以依赖类型系统为基础的编程语言大多同时也作为构造证明与可验证程序的辅助工具而存在，如 Coq 和 Agda（但并非所有证明辅助工具都以类型论为基础）；近年来，一些以通用和系统编程为目的的编程语言被设计出来，如 Idris。
>
> 一些以证明辅助为主要目的的编程语言采用[强函数式编程](https://zh.wikipedia.org/wiki/%E5%BC%BA%E5%87%BD%E6%95%B0%E5%BC%8F%E7%BC%96%E7%A8%8B "强函数式编程")（total functional programming），这消除了停机问题，同时也意味着通过它们自身的核心语言无法实现任意无限递归，不是[图灵完全](https://zh.wikipedia.org/wiki/%E5%9B%BE%E7%81%B5%E5%AE%8C%E5%85%A8 "图灵完全")的，如 Coq 和 Agda；另外一些依赖类型编程语言则是图灵完全的，如 Idris、由 [ML](https://zh.wikipedia.org/wiki/ML%E8%AF%AD%E8%A8%80 "ML语言") 派生而来的 ATS 和 由 [F#](https://zh.wikipedia.org/wiki/F%E2%99%AF "F♯") 派生而来的 F*。
>
>> **强函数式编程**（也称为**全函数式编程**），^[[1]](https://zh.wikipedia.org/wiki/%E5%BC%BA%E5%87%BD%E6%95%B0%E5%BC%8F%E7%BC%96%E7%A8%8B#cite_note-1)^与之相对的是普通的或者说弱[函数式编程](https://zh.wikipedia.org/wiki/%E5%87%BD%E6%95%B0%E5%BC%8F%E7%BC%96%E7%A8%8B "函数式编程")。是一种[编程](https://zh.wikipedia.org/wiki/%E7%A8%8B%E5%BA%8F%E8%AE%BE%E8%AE%A1 "程序设计")范式，它将程序的范围限制为[可证明停机的程序](https://zh.wikipedia.org/wiki/%E5%88%A4%E5%AE%9A%E5%99%A8 "判定器")。 ^[[2]](https://zh.wikipedia.org/wiki/%E5%BC%BA%E5%87%BD%E6%95%B0%E5%BC%8F%E7%BC%96%E7%A8%8B#cite_note-TFP-2)^
>>

### 使用策略编程

如果我们可以通过显式地给出项，而不是执行策略脚本，来构造证明，你可能会好奇我们是否可以通过*'策略'*，而不是显式地给出项，来构造*'程序'*。 自然地，答案是可以！

```coq
Definition add1 : nat -> nat.
intro n.
Show Proof.   (* (fun n : nat => ?Goal) *)
apply S.
Show Proof.   (* (fun n : nat => S ?Goal) *)
apply n. Defined.

Print add1.
(* ==>
    add1 = fun n : nat => S n
         : nat -> nat
*)

Compute add1 2.
(* ==> 3 : nat *)
```

注意到我们通过使用**.**终止了**Definition**，而不是使用**:=**和一个项来定义它。这个记号会告诉Coq进入*'证明脚本模式(Proof Scripting Mode)'*来构造类型是**nat** **→** **nat**的项。并且，<u>我们通过使用</u>​<u>**Defined**</u>​<u>而不是 ​</u>​<u>**Qed**</u>​<u>来终止证明；这使得这个定义是</u>​==<u>*'透明的(Transparent)'*</u>==​<u>，所以它可以在计算中就像正常定义的函数一样被使用。（通过</u>​<u>**Qed**</u>​<u>定义的对象在计算中是不透明的。）</u>#TODO#​

这个特性主要是在定义拥有依赖类型的函数时非常有用。我们不会在本书中详细讨论后者。但是它确实表明了Coq里面基本思想的一致性和正交性。

‍

### 逻辑联结词作为归纳类型

归纳定义足够用于表达我们目前为止遇到的大多数的联结词。<u>事实上， 只有全称量化（以及作为特殊情况的蕴含式）是 Coq 内置的，所有其他的都是被归纳定义的。</u>在这一节中我们会看到它们的定义。

#### 合取

为了证明**P** **∧** **Q**成立，我们必须同时给出**P**和**Q**的证据。因此，我们可 以合理地将**P** **∧** **Q**的证明对象定义为包含两个证明的元祖：一个是**P**的证明，另一个是**Q**的证明。即我们拥有如下定义。

```coq
Inductive and (P Q : Prop) : Prop :=
| conj : P -> Q -> and P Q.
```

注意到这个定义与在章节 [Poly](https://coq-zh.github.io/SF-zh/lf-current/Poly.html) 中给出的 **prod** 定义的类型的相似处； 唯一的不同之处在于，**prod**的参数是 **Type**，而 **and ​**的类型是 **Prop**。

```coq
Print prod.
(* ===>
   Inductive prod (X Y : Type) : Type :=
   | pair : X -> Y -> X * Y. *)
```

这个定义能够解释为什么 **destruct ​**和 **intros ​**模式能用于一个合取前提。 情况分析允许我们考虑所有**P** **∧** **Q**可能被证明的方式——只有一种方式（即 ==**conj ​**==​==构造子==）。`| conj : P -> Q -> and P Q.`​

> ​#GPT#​ conj 来源于英语单词 conjunction，意思是“连接，连结”。它是一个 Prop 类型（数学上用来表示命题是真的，或者模型中的数据满足一些关系）的操作符，可以将两个命题组合成一个，这意味着它们必须同时为真。换句话说，一个 conj 就是一个共享了同一个 Introduction 证明过程 P /\ Q 的两个子目标 P 和 Q，它们之间没有中间状态。

类似地，==**split ​**==​==策略==能够用于所有只有一个构造子的归 纳定义命题。特别地，它能够用于**and**：

```coq
Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HQ HP]. split.
    + apply HP.
    + apply HQ.
Qed.

```

这解释了为什么一直以来我们能够使用策略来操作 **and ​**的归纳定义。我们也可以使用模式匹配来用它直接构造证明。例如：

```coq
Definition and_comm'_aux P Q (H : P /\ Q) : Q /\ P :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).
(* <-> 是 <- 与 -> 的合取  *)
```

构造一个证明对象来证明下列命题。

```coq
Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R
  (* 将本行替换成 ":= _你的_定义_ ." *) :=
  fun (P Q R:Prop) (HPQ:P /\ Q) (HQR:Q /\ R) => 
  match HPQ, HQR with 
  | conj HP HQ , conj HQ2 HR => conj HP HR
  end.
(* TODO 有待理解，为什么就直接产生证实了 *)
```

‍

#### 析取

析取的归纳定义有两个构造子，分别用于析取的两边：

```coq
Inductive or (P Q : Prop) : Prop :=
| or_introl : P -> or P Q
| or_intror : Q -> or P Q.
```

这个声明解释了**destruct**策略在一个析取前提上的行为，产生的子类型和 **or_introl ​**以及 **or_intror**构造子的形状相匹配。

又一次地，我们可以不使用策略，直接写出涉及**or**的定义的证明对象。

尝试写下**or_commut**的显式证明对象。（不要使用**Print**来偷看我们已经 定义的版本！）

```coq
(* 我就偷看 ;-) *)
Print or_comm.
(* or_comm = 
fun A B : Prop =>
conj
  (fun H : A \/ B =>
   match H with
   | or_introl x => (fun H0 : A => or_intror H0) x
   | or_intror x => (fun H0 : B => or_introl H0) x
   end)
  (fun H : B \/ A =>
   match H with
   | or_introl x => (fun H0 : B => or_intror H0) x
   | or_intror x => (fun H0 : A => or_introl H0) x
   end)
	 : forall A B : Prop, A \/ B <-> B \/ A

Arguments or_comm (A B)%type_scope
 *)
Print or_commut.
(* or_commut = 
fun (P Q : Prop) (H : P \/ Q) =>
match H with
| or_introl x => (fun HP : P => or_intror HP) x
| or_intror x => (fun HQ : Q => or_introl HQ) x
end
	 : forall P Q : Prop, P \/ Q -> Q \/ P

Arguments or_commut (P Q)%type_scope _
 *)
Definition or_comm : forall P Q, P \/ Q -> Q \/ P
  (* 将本行替换成 ":= _你的_定义_ ." *)  :=
  fun (P Q : Prop) (pq: P \/ Q) =>
  match pq with
    | or_introl p => or_intror Q p
    | or_intror q => or_introl P q
  end.
```

‍

#### 存在量化

为了给出存在量词的证据，我们将一个证据类型**x**和**x**满足性质**P**的证明打包在一起：

```coq
Inductive ex {A : Type} (P : A -> Prop) : Prop :=
| ex_intro : forall x : A, P x -> ex P.
```

打包之后的命题可以通过解包操作受益。这里的核心定义是为了用于构造 **ex** **P**命题的类型构造器**ex**，其中**P**自身是一个从类型为**A**的证据类型 值到命题的*'函数(Function)'*。构造子**ex_intro**提供了一个给定证据类型**x**和**P** **x**的证明，可以构造**ex** **P**的证据的方式。

我们更加熟悉的类型**∃** **x**, **P** **x**可以转换为一个涉及**ex**的表达式：

```coq
Check ex (fun n => ev n) : Prop.
```

下面是我们如何定义一个涉及**ex**的显式证明对象：

```coq
Definition some_nat_is_even : exists n, ev n :=
  ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_0)).
```

```coq
(** **** 练习：2 星, standard, optional (ex_ev_Sn) 

    完成下列证明对象的定义： *)

Definition ex_ev_Sn : ex (fun n => ev (S n))
  (* 将本行替换成 ":= _你的_定义_ ." *). Admitted.
(* TODO 有待理解 *)

```

​#TODO#​

#### True 和 False

**True**命题的归纳定义很简单：

```coq
Inductive True : Prop :=
  | I : True.
```

它拥有一个构造子（因此**True**的所有证据都是一样的，所以给出一个 **True**的证明并没有信息量。）

False也一样的简单——事实上，它是如此简单，以致于第一眼看上去像是一个 语法错误。

```coq
Inductive False : Prop := .
```

也就是说， **False**是一个*'没有'*构造子的归纳类型--即，没有任何方式能 够构造一个它的证明。

‍

### 相等关系

在Coq里，甚至连相等关系都不是内置的。它拥有如下的归纳定义。（事实上， 在标准库里的定义是这里给出的定义的轻微变体，前者给出了稍微容易使用 一些的归纳法则。）

```coq
Inductive eq {X:Type} : X -> X -> Prop :=
| eq_refl : forall x, eq x x.

Notation "x == y" := (eq x y)
                    (at level 70, no associativity)
                    : type_scope.
```

我们可以这样理解这个定义，给定一个集合**X**，它定义了由**X**的一对值 (**x**和**y**)所索引的“**x**与**y**相等”的一*'系列(Family)'*的命题。只有 一种方式能够构造该系列中成员的证据：将构造子**eq_refl**应用到类型**X** 和值**x**:**X**，产生一个**x**等于**x**的证据。

其它形如 **eq** **x** **y** 的类型中的 **x** 和 **y** 并不相同，<u>因此是非居留的</u>。#疑惑#​ 意思是 非相等的？

我们可以使用**eq_refl**来构造证据，比如说，**2** **=** **2**。那么我们能否使用 它来构造证据**1** **+** **1** **=** **2**呢？答案是肯定的。事实上，它就是同一个证据！

原因是<u>如果两个项能够通过一些简单的计算规则</u>​==<u>*'可转换(convertible)'*</u>==​==<u>​ ​</u>==​<u>， 那么Coq认为两者“相等”。</u>

这些计算规则，与**Compute**所使用的规则相似，包括函数应用的计算，定义的内联，**match**语句的化简。

```coq
Lemma four: 2 + 2 == 1 + 3.
Proof.
  apply eq_refl.
Qed.
```

<u>至今为止我们所用来证据相等关系的 ​</u>​<u>**reflexivity ​**</u>​<u>策略本质上只是 ​</u>​<u>**apply**</u>​<u>​ ​</u>​<u>**eq_refl ​**</u>​<u>的简写</u>。

> ​#疑惑#​  `=`​ 与 `==`​ 的关系？实测 `reflexivity`​ 只能证明 `=`​。猜测 `==`​ 只是为了临时举例子用？
>
> ```coq
> (* TODO coq 中 `=` 与 `==` 的关系？
> 实测 `reflexivity` 只能证明 `=` *)
> Lemma four_': 2 + 2 = 1 + 3.
> Proof. reflexivity. Qed.
>
> Lemma four_f: 2 + 2 == 1 + 3.
> Proof.
>   Fail reflexivity.
> ```

在基于策略的相等关系证明中，转换规则通常隐藏在**simpl**的使用后面（在 其他策略中或显式或隐式，例如**reflexivity**）。

而在如下的显式证明对象中，你可以直接看到它们：

```coq
Definition four' : 2 + 2 == 1 + 3 :=
  eq_refl 4.

Definition singleton : forall (X:Type) (x:X), []++[x] == x::[]  :=
  fun (X:Type) (x:X) => eq_refl [x].
```

相等关系的归纳定义隐含了*'Leibniz相等关系(Leibniz equality)'*：当我们 说“**x**和**y**相等的时候”，我们意味着所有**x**满足的性质**P**，对于**y** 来说也满足。事实上，相等关系的归纳定义和Leibniz相等关系是 *'等价的(equivalent)'*。

```coq
(** **** 练习：2 星, standard (equality__leibniz_equality) 

    相等关系的归纳定义隐含了_'Leibniz相等关系(Leibniz equality)'_：当我们
    说“[x]和[y]相等的时候”，我们意味着所有[x]满足的性质[P]，对于[y]
    来说也满足。 *)

Lemma equality__leibniz_equality : forall (X : Type) (x y: X),
  x == y -> forall P:X->Prop, P x -> P y.
Proof.
(* 请在此处解答 *) Admitted.
(** [] *)

(** **** 练习：5 星, standard, optional (leibniz_equality__equality) 

    请说明，事实上，相等关系的归纳定义和Leibniz相等关系是
    _'等价的(equivalent)'_。 *)

Lemma leibniz_equality__equality : forall (X : Type) (x y: X),
  (forall P:X->Prop, P x -> P y) -> x == y.
Proof.
(* 请在此处解答 *) Admitted.

```

‍

#### 再论反演

​#TODO#​ *一点都没学*

我们曾经见过**inversion ​**被同时用于相等关系前提，和关于被归纳定义的命题的前提。现在我们明白了实际上它们是同一件事情。那么我们现在可以细 究一下**inversion**是如何工作的。

一般来说，**inversion**策略...

* 接受一个前提**H**，该前提的类型**P**是通过归纳定义的，以及
* 对于**P**的定义里的每一个构造子**C**，

  * 产生一个新的子目标，在该子目标中我们假设**H**是通过**C**构造的，
  * 作为额外的假设，在子目标的上下文中增加**C**的论据（前提），
  * 将**C**的结论（结果类型）与当前的目标相匹配，计算出为了能够应用**C**而必须成立的一些相等关系，
  * 将这些相等关系加入上下文中（以及，为了方便，在目标中替换它们），以及
  * 如果这些相等关系无法满足（例如，它们涉及到**S** **n** **=** **O**），那么立即解决这个子目标。

*'例子'*：如果我们反演一个使用**or**构造的前提，它有两个构 造子，所以产生了两个子目标。构造子的结论（结果类型，即**P** **∨** **Q**） 并没有对于**P**和**Q**的形式有任何要求，所以在子目标的上下文中我们不会 获得额外的相等关系。

*'例子'*：如果我们反演一个使用**and**构造的前提，它只有一个构造子， 所以只产生一个子目标。再一次地，构造子的结论（结果类型，即**P** **∧** **Q**） 并没有对于**P**和**Q**的形式有任何要求，所以在子目标的上下文中我们不会 获得额外的相等关系。不过，这个构造子有两个额外的参数，我们能够在子 目标的上下文中看到它们。

*'例子'*：如果我们反演一个使用**eq**构造的前提，它也只有一个构造子， 所以只产生一个子目标。但是，现在**eq_refl**构造子的形式给我们带来 的额外的信息：它告诉**eq**的两个参数必须是一样的。于是**inversion ​**策略会将这个事实加入到上下文中。

‍
