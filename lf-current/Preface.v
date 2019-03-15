(** * Preface: 前言 *)

(* ################################################################# *)
(** * 欢迎 *)

(** 这里是一系列关于_'软件基础'_各个方面的电子书的起点，它阐明了可靠软件背后的数学根基。
    书中的主题包括基本的逻辑概念、计算机辅助定理证明、Coq 证明助理、
    函数式编程、操作语义、用来对软件进行论证的逻辑以及静态类型系统。
    本课程的目标受众包括从高年级本科生到博士生和研究者的广大读者。
    书中并未假定读者有逻辑学或编程语言的背景，不过一定的数学熟练度会很有帮助。

    本课程最大的创新之处在于，所有内容都百分之百地形式化且通过了机器验证。
    也就是说，所有的内容都是字面意义上的 Coq 脚本，旨在配合 Coq
    的交互式会话一起阅读。书中的所有细节都用 Coq 完全形式化了，习题也被设计成用
    Coq 来解答。

    每卷书中文件都经过了精心组织：核心章节作为主线贯穿始终，涵盖了一学期的内容；
    “支线”中则包含附加的主题。所有核心章节都适合高年级本科生和研究生。

    本书为第一卷_'《逻辑基础》'_，它向读者介绍了函数式编程的基本概念、构造逻辑以及
    Coq 证明助理，为其它卷本的学习奠定了基础。 *)

(* ################################################################# *)
(** * 概览 *)

(** 构建可靠的软件非常困难。现代系统的规模、复杂度、参与构建过程的人数，
    还有置于系统之上的需求范围，让构建或多或少地正确的软件变得极为困难，
    更不用说百分之百地正确了。同时，由于信息处理技术继续渗透到社会的各个层面，
    人们为程序错误和漏洞付出的代价变得越来越高昂。

    为了应对这些挑战，计算机科学家和软件工程师们发展了一系列提升软件质量的方法，
    从为管理软件项目的团队提供建议（如极限编程，Extreme Programming），
    到库的设计原理（如模型-视图-控制器，Model-View-Controller；发布-订阅模式，
    Publish-Subscribe）以及编程语言的设计哲学（面向对象编程，Object Oriented Programmin；
    面向剖面编程，Aspect Oriented Programming；函数式编程，Functional Programming），
    还有用于阐明和论证软件性质的数学技术，以及验证这些性质的工具。
    _'《软件基础》'_系列着重于最后一种方法。

    本书将以下三种概念穿插在一起：

    （1）_'逻辑学'_中的基本工具，用于准确地提出并论证关于程序的假设；

    （2）_'证明助理'_用于构造严谨的逻辑论据；

    （3）_'函数式编程'_思想，同时作为一种编程方法来简化程序的论证，
         以及架起程序和逻辑学之间的桥梁。

    建议的扩展阅读可在 [Postscript] 一章中找到；
    所有引用过的著作书目信息可以在 [Bib] 一章中找到。 *)

(* ================================================================= *)
(** ** 逻辑学 *)

(** 逻辑学是研究_'证明'_的领域，即对特定命题的真伪性进行不容置疑的论证。
    有关逻辑学在计算机科学中核心作用的书卷汗牛充栋。Manna 和 Waldinger
    称之为“计算机科学的微积分”，而 Halpern 的论文
    _'On the Unusual Effectiveness of Logic in Computer Science'_
    中则收录了大量逻辑学为计算机科学提供的洞察力和至关重要的工具。
    的确，他们发现：“实际上，逻辑学对计算机科学来说远比在数学中更加有效。
    这相当引人注目，特别是过去一百年来，逻辑学发展的动力大都来自于数学。”

    具体来说，_'归纳证明'_的基本概念在计算机科学中无处不在。
    你以前肯定见过它们，比如说在离散数学或算法分析中。不过在本课程中，
    我们会在你未曾涉及的深度下对它进行探讨。 *)

(* ================================================================= *)
(** ** 证明助理 *)

(** 逻辑学和计算机科学之间的思想交流并不是单向的，
    计算机科学也为逻辑学做出了重要的贡献，
    其中之一就是发展了帮助逻辑命题构造证明的软件工具。
    这些工具分为两大类：

       - _'自动定理证明器'_ 提供了一键式操作：它们接受一个命题，
         然后返回_'真'_或_'假'_（有时为_'未知：超时'_ ）。
         尽管它们的能力仅限于特定种类的推理，然而在近几年却快速成熟，
         并应用到了多种场景中。此类工具包括 SAT 求解器，SMT 求解器以及模型检查器
         （Model Checker）。

       - _'证明助理'_ 是一种混合式工具，它能将证明的构建中比较常规的部分自动化，
         而更加困难的部分则依赖人类来解决。广泛使用的证明助理包括
         Isabelle、Agda、Twelf、ACL2、PVS 以及 Coq 等等。

    本课程围绕 Coq 展开，它是个自 1983 年以来主要在法国开发的证明助理，
    近年来吸引了大量来自研究机构和业界的社区用户。
    Coq 为机器验证的形式化论证的交互式开发提供了丰富的环境。Coq
    系统的内核是一个简单的证明检查器，它保证只会执行正确的推理步骤。
    在此内核之上，Coq 环境提供了高级的证明开发功能，包括一个庞大的库，
    其中包含各种定义和引理；强大策略，用于半自动化构造证明；
    还有一个专用的编程语言，能够为特殊情况定义新的自动证明策略。

    Coq 已成为跨计算机科学和数学研究的关键推动者：

    - 作为一个_'编程语言的建模平台'_，
      Coq 成为了研究员对复杂的语言定义进行描述和论证的标准工具。
      例如，它被用来检查 JavaCard 平台的安全性，得到了最高等级的通用准则验证，
      它还被用在 x86 和 LLVM 指令集以及 C 等编程语言的形式化规范中。

    - 作为一个_'形式化软件验证的开发环境'_，Coq 被用来构建：
      CompCert，一个完全验证的 C 优化编译器；
      CertiKos，一个完全验证的工具，用于证明涉及浮点数的精妙算法的正确性；
      Coq 也是 CertiCrypt 的基础，一个用于论证密码学算法安全性的环境。
      Coq 还被用来构建开源 RISC-V 处理器的验证实现。

    - 作为一个_'依赖类型函数式编程的现实环境'_，Coq 激发了大量的创新。
      例如 Ynot 系统嵌入了“关系式霍尔推理”（一个 _'霍尔逻辑'_ 的扩展，
      我们之后会看到它）。

    - 作为一个_'高阶逻辑的证明助理'_，Coq 被用来验证数学中一些重要的结果。
      例如 Coq 可在证明中包含复杂计算的能力，使其开发出了第一个形式化验证的四色定理证明。
      此前数学家们对该证明颇有争议，因为其中一部分用程序对大量组态进行了检验。
      在 Coq 的形式化中，所有东西都被检验过，自然也包括计算的正确性。
      近年来，Feit-Thompson 定理经过了更大的努力用 Coq 形式化了，
      它是对有限单群进行分类的十分重要的第一步。

   顺便一提，如果你对 Coq 这个名字感到好奇，INRIA (法国国家研究实验室，Coq
   主要在这里开发）上的 Coq 官方网站给出了解释：
   “一些法国计算机科学家有用动物命名软件的传统：像 Caml、Elan、Foc、Phox
   都心照不宣地遵循这种默契。在法国，“Coq”是雄鸡，发音也像构造演算
   （Calculus of Constructions）的首字母缩写（CoC），它是 Coq 的基础。”
   高卢雄鸡是法国的象征。C-o-q 还是 Thierry Coquand 名字的前三个字母，
   他是 Coq 的早期开发者之一。 *)

(* ================================================================= *)
(** ** 函数式编程 *)

(** _'函数式编程'_不仅表示可以在几乎任何编程语言中使用的各种习语（Idiom），
    还代表着一族以这些习语为侧重点设计的编程语言，包括
    Haskell、OCaml、Standard ML、F##、Scala、Scheme、Racket、Common Lisp、Erlang
    还有 Coq。

    函数式编程已经有数十年的历史了--实际上，它甚至可以追溯到 1930
    年代 Church 发明的 λ-演算，那时还没有计算机呢！自 90 年代初以来，
    函数式编程激起了业内软件工程师和语言设计者浓厚的兴趣，它们还在
    Jane St. Capital、Microsoft、Facebook 和 Ericsson
    等公司的高价值系统中发挥着关键的作用。

    函数式编程最根本的原则是，计算应当尽可能地_'纯粹'_，也就是说，
    执行代码的唯一作用应当是只产生一个结果。计算应当没有_'副作用'_，
    即它与输入/输出、可变量的赋值、指针重定向等相分离。例如，_'指令式'_
    的排序函数会接受一个数字列表，通过重组指针使列表得以排序；
    而一个纯粹的排序函数则会接受一个列表，返回一个含有同样数字，
    但是已经排序的新列表。

    这种编程风格最明显的好处之一，就是它能让程序变得更容易理解和论证。
    如果对某个数据结构的所有操作都会返回新的数据结构，而旧有的结构没有变动，
    那么我们便无需担心它的共享方式，因为程序中一部分的改变并不会破坏另一部分的属性。
    在并发程序中，线程间共享的每一个可变状态都是致命 Bug 的潜在来源，
    因此这方面的考虑尤为关键。事实上，业界最近对函数式编程的兴趣大部分来源于此，
    即它在并发中表现出的简单行为。

    人们对函数式编程感到兴奋的另一原因与前文所述的原因相关：
    函数式程序通常比指令式程序更容易并行化。
    如果一个计算除了产生结果之外没有其它的作用，那么它在 _'何时'_
    执行便不再重要。同样，如果一个数据结构不会被破坏性地修改，
    那么它可以跨核心或网络地被随意复制。其实，“映射-归约”（Map-Reduce）
    的惯用法就是函数式编程的经典例子，它在大规模分布式查询处理器（如 Hadoop）
    中处于核心地位，并被 Google 用来索引整个互联网。

    对本课程而言，函数式编程还有另一个重要的吸引力：
    它在逻辑和计算机科学之间架起了一座桥梁。事实上，Coq
    本身即可视作一个小巧却有着极强表达能力的函数式编程语言，
    以及一组用于陈述和证明逻辑断言的工具的结合体。进而言之，
    当我们更加深入地审视它时，会发现 Coq 的这两方面其实基于完全相同的底层机制 --
    _'命题即类型，程序即证明'_，可谓殊途同归。 *)

(* ================================================================= *)
(** ** 扩展阅读 *)

(** 本书旨在自成一体，不过想要对特定主题进行深入研究的读者，可以在
    [Postscript] 一章中找到推荐的扩展阅读。 *)

(* ################################################################# *)
(** * 实践指南 *)

(* ================================================================= *)
(** ** 章节依赖 *)

(** 章节之间的依赖关系图以及建议的学习路线可以在文件
    [deps.html]
    中查看。 *)

(* ================================================================= *)
(** ** 系统要求 *)

(** Coq 可以在 Windows、Linux 和 macOS 上运行。我们需要：

       - 安装近期版本的 Coq，它可以从 Coq 主页获得。本书中的文件均已通过了
         Coq 8.8.1 的测试。

       - 一个能跟 Coq 交互的 IDE。目前有两种选择：

           - Proof General 是一个基于 Emacs 的 IDE，Emacs 用户应该更喜欢这个。
             它需要单独安装（Google 搜索“Proof General”）。

             爱作死的 Emacs 党也可以试试 [company-coq] 和 [control-lock]
             之类的扩展。

           - CoqIDE 是个更加简单的独立 IDE。它随 Coq 一起发布，
             所以如果你安装了 Coq，它应该就能用。你也可以从头编译安装它，
             不过在某些平台上还需要额外安装 GUI 之类的库。

             用户在运行 CoqIDE 时可以考虑关闭“异步”和“错误恢复”模式：

  coqide -async-proofs off -async-proofs-command-error-resilience off Foo.v &
*)

(* ================================================================= *)
(** ** 练习 *)

(** 每一章都包含大量的习题。每个习题都有标有“星级”，其含义是：

       - 一星：很简单习题，强调课程的重点。对于大部分读者而言，
         一两分钟应该足够了。养成看到一个做一个的习惯。

       - 二星：直截了当的习题（5 到 10 分钟）。

       - 三星：需要一点思考的习题（10 分钟到半小时）。

       - 四或五星：更加困难的习题（半小时以上）。

    此外，有些习题标注为“进阶”，有些习题标注为“可选”。
    只做非进阶、非可选的习题已经能将核心概念掌握得很不错了。
    可选习题会对一些关键概念提供额外的练习，还有一些读者可能会感兴趣的次级主题。
    进阶练习则留给想要更多挑战和更深理解的读者。

     _'请勿公布习题解答！'_ 

    《软件基础》已被广泛地用作自学教程和大学课程。如果习题解答很容易获得，
    那么本书的效用将大打折扣，对于会为作业评分的大学课程来说尤其如此。
    我们特别请求读者，切勿将习题答案放在任何能够被搜索引擎找到的地方。 *)

(* ================================================================= *)
(** ** 下载 Coq 文件 *)

(** 本书的“英文发布版”以及所有源代码的压缩包
    （其中包含一组 Coq 脚本和 HTML 文件）可访问
    http://softwarefoundations.cis.upenn.edu 获取。

    本书的中文版和压缩包可访问 https://github.com/Coq-zh/SF-zh 获取。

    （如果你是在一门课程中使用本书的，那么你的教授可能会让你使用本地的修改版，
    此时你应当使用它们而非发布版，这样你可以获得所有该学期的本地更新。） *)

(* ################################################################# *)
(** * 资源 *)

(* ================================================================= *)
(** ** 模拟题 *)

(** 宾夕法尼亚大学的 CIS500（软件基础）课程提供了大量的考试大纲，可访问
    https://www.seas.upenn.edu/~cis500/current/exams/index.html 获取。
    近年来书中的记法有所变动，但大部分问题仍与本文对应。 *)

(* ================================================================= *)
(** ** 课程视频 *)

(** _'《逻辑基础》'_夏季加强班（DeepSpec 夏季班系列之一）的课程讲义可访问
    https://deepspec.org/event/dsss17 和 https://deepspec.org/event/dsss18/
    获取。2017 年的视频清晰度不高，但在之后的课程中会更好。 *)

(* ################################################################# *)
(** * 对授课员的要求 *)

(** 如果您有意用这些课件授课，那肯定会发现希望改进、提高或增加的材料。
    我们欢迎您的贡献！

    为保证法律上的简单性和单一责任制，任何情况下都不应出现许可协议条款的的调整，
    授权的转移等等，我们要求所有贡献者（即，任何可访问开发者仓库的人）根据
    “作者记录”为他们的贡献赋予如下版权信息：

      - I hereby assign copyright in my past and future contributions
        to the Software Foundations project to the Author of Record of
        each volume or component, to be licensed under the same terms
        as the rest of Software Foundations.  I understand that, at
        present, the Authors of Record are as follows: For Volumes 1
        and 2, known until 2016 as "Software Foundations" and from
        2016 as (respectively) "Logical Foundations" and "Programming
        Foundations," and for Volume 4, "QuickChick: Property-Based
        Testing in Coq," the Author of Record is Benjamin C. Pierce.
        For Volume 3, "Verified Functional Algorithms", the Author of
        Record is Andrew W. Appel. For components outside of
        designated volumes (e.g., typesetting and grading tools and
        other software infrastructure), the Author of Record is
        Benjamin Pierce.

    To get started, please send an email to Benjamin Pierce,
    describing yourself and how you plan to use the materials and
    including (1) the above copyright transfer text and (2) your
    github username.

    We'll set you up with access to the git repository and developers'
    mailing lists.  In the repository you'll find a file [INSTRUCTORS]
    with further instructions. *)

(* ################################################################# *)
(** * 译本 *)

(** 感谢翻译志愿者团队的努力，_'《软件基础》'_
    已有日文版可以享用 http://proofcafe.org/sf。
    中文版还在填坑= =|| *)

(* ################################################################# *)
(** * 鸣谢 *)

(** _'《软件基础》'_ 系列的开发，部分由国家科学基金会
    （National Science Foundation）在 NSF 科研赞助 1521523 号
    _'深度规范科学'_ 下提供支持。 *)

(* Fri Mar 15 16:36:25 UTC 2019 *)
