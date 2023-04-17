---
title: ImpCEvalFun
date: 2023-04-17T13:19:34Z
lastmod: 2023-04-17T14:05:00Z
---

# ImpCEvalFun

# Imp 的求值函数    (ImpCEvalFun)

* [一个无法完成的求值器](https://coq-zh.github.io/SF-zh/lf-current/ImpCEvalFun.html#lab385)
* [一个计步的求值器](https://coq-zh.github.io/SF-zh/lf-current/ImpCEvalFun.html#lab386)
* [关系求值 vs. 计步求值](https://coq-zh.github.io/SF-zh/lf-current/ImpCEvalFun.html#lab389)
* [再论求值的确定性](https://coq-zh.github.io/SF-zh/lf-current/ImpCEvalFun.html#lab392)

在[Imp](https://coq-zh.github.io/SF-zh/lf-current/Imp.html)一章中我们已经见到了直接为 **Imp** 定义求值函数时会遇到的困难。 当时为了规避这些困难，我们选择了定义<u>求值关系</u>而不是函数。 而在这一可选的章节中，我们会再次讨论能够实现 **Imp** <u>求值函数</u>的方法。

## 一个无法完成的求值器

在初次为指令编写求值函数时（求值作为函数（失败的尝试）），我们写出了如下忽略了 **WHILE** 的代码：

```coq
Open Scope imp_scope.
Fixpoint ceval_step1 (st : state) (c : com) : state :=
  match c with
    | SKIP =>
        st
    | l ::= a1 =>
        (l !-> aeval st a1 ; st)
    | c1 ;; c2 =>
        let st' := ceval_step1 st c1 in
        ceval_step1 st' c2
    | TEST b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_step1 st c1
          else ceval_step1 st c2
    | WHILE b1 DO c1 END =>
        st  (* bogus 假的 *)
  end.
Close Scope imp_scope.
```

如[Imp](https://coq-zh.github.io/SF-zh/lf-current/Imp.html)一章中所言，在 ML 或 Haskell 这类传统的函数式语言中， 我们可以这样处理 **WHILE** 指令：

```coq
    | WHILE b1 DO c1 END =>
        if (beval st b1) then
          ceval_step1 st (c1;; WHILE b1 DO c1 END)
        else st
```

Coq 不会接受此定义（它会提示出现错误 **Error**: **Cannot** **guess** **decreasing** **argument** **of** **fix**），因为我们想要定义的函数无需保证一定停机。 确实，修改后的 **ceval_step1** 应用到 **Imp.v** 中的 **loop** 程序时永远不会停机。 因为 Coq 不仅是一个函数式编程语言，还拥有逻辑一致性， 因此任何有可能不会停机的函数都会被拒绝。下面是一段无效的(!) Coq 程序，它展示了假如 Coq 允许不停机的递归函数时会产生什么错误：

```coq
Fixpoint loop_false (n : nat) : False := loop_false n.
```

也就是说，像 **False** 这样的命题会变成可证的（例如 **loop_false** **0** 就是个对 **False** 的证明），这对 Coq 的逻辑一致性来说是一场灾难。

由于它不会对所有的输入停机，因此至少在不借助附加技巧的情况下， **ceval_step1** 的完整版本无法用 Coq 写出...

## 一个计步的求值器

我们需要的技巧是将一个*'附加'*的参数传入求值函数中来告诉它需要运行多久。 非正式地说，我们会在求值器的“油箱”中加一定数量的“汽油”， 然后允许它运行到按一般的方式终止*'或者'*耗尽汽油， 此时我们会停止求值并说最终结果为空内存（empty memory）。 （我们也可以说当前的状态为求值器耗尽了汽油 -- 这无关紧要， 因为无论在哪种情况下结果都是错误的！）

```coq
Open Scope imp_scope.
Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with
  | O => empty_st
  | S i' =>
    match c with
      | SKIP =>
          st
      | l ::= a1 =>
          (l !-> aeval st a1 ; st)
      | c1 ;; c2 =>
          let st' := ceval_step2 st c1 i' in
          ceval_step2 st' c2 i'
      | TEST b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step2 st c1 i'
            else ceval_step2 st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then let st' := ceval_step2 st c1 i' in
               ceval_step2 st' c i'
          else st
    end
  end.
Close Scope imp_scope.
```

*'注意'*：很容易想到这里的索引 **i** 是用来计算“求值的步数”的。 然而我们仔细研究就会发现实际并非如此。例如，在串连的规则中，同一个 **i** 被传入了两个递归调用中。正确地理解 **i** 对于 **ceval__ceval_step** 的正式名分重要，它会在下面的练习中给出。

此求值器不太好的一点就是我们无法根据其结果说它是否停止， 因为程序可能是正常停机，也可能是耗尽了汽油。我们的下下一个版本会<u>返回一个 ​</u>​<u>**option**</u>​<u>​ ​</u>​<u>**state**</u>​<u>​ 而非只是一个 ​</u>​<u>**state**</u>，这样我们就能区分正常和异常的停机了。

```coq
Open Scope imp_scope.
Fixpoint ceval_step3 (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | SKIP =>
          Some st
      | l ::= a1 =>
          Some (l !-> aeval st a1 ; st)
      | c1 ;; c2 =>
          match (ceval_step3 st c1 i') with
          | Some st' => ceval_step3 st' c2 i'
          | None => None
          end
      | TEST b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step3 st c1 i'
            else ceval_step3 st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then match (ceval_step3 st c1 i') with
               | Some st' => ceval_step3 st' c i'
               | None => None
               end
          else Some st
    end
  end.
Close Scope imp_scope.
```

我们可以引入一些辅助记法来隐藏对可选状态进行重复匹配的复杂工作， 从而提高此版本的可读性。

```coq
Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).

Open Scope imp_scope.
Fixpoint ceval_step (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | SKIP =>
          Some st
      | l ::= a1 =>
          Some (l !-> aeval st a1 ; st)
      | c1 ;; c2 =>
          LETOPT st' <== ceval_step st c1 i' IN
          ceval_step st' c2 i'
      | TEST b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
          else Some st
    end
  end.
Close Scope imp_scope.

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None    => None
  | Some st => Some (st X, st Y, st Z)
  end.

Compute
(test_ceval empty_st
    (X ::= 2;;
      TEST (X <= 1)
        THEN Y ::= 3
        ELSE Z ::= 4
      FI)).
(*    ====>
      Some (2, 0, 4)   *)
```

​#剩余习题未完成#​

## 关系求值 vs. 计步求值

对于算术表达式和布尔表达式，我们希望两种求值的定义最终都能产生同样的结果。 本节将对此说明。

```coq
Theorem ceval_step__ceval: forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      st =[ c ]=> st'.
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i' ].

  - (* i = 0 -- contradictory *)
    intros c st st' H. discriminate H.

  - (* i = S i' *)
    intros c st st' H.
    destruct c;
           simpl in H; inversion H; subst; clear H.
      + (* SKIP *) apply E_Skip.
      + (* ::= *) apply E_Ass. reflexivity.

      + (* ;; *)
        destruct (ceval_step st c1 i') eqn:Heqr1.
        * (* Evaluation of r1 terminates normally *)
          apply E_Seq with s.
            apply IHi'. rewrite Heqr1. reflexivity.
            apply IHi'. simpl in H1. assumption.
        * (* Otherwise -- contradiction *)
          discriminate H1.

      + (* TEST *)
        destruct (beval st b) eqn:Heqr.
        * (* r = true *)
          apply E_IfTrue. rewrite Heqr. reflexivity.
          apply IHi'. assumption.
        * (* r = false *)
          apply E_IfFalse. rewrite Heqr. reflexivity.
          apply IHi'. assumption.

      + (* WHILE *) destruct (beval st b) eqn :Heqr.
        * (* r = true *)
         destruct (ceval_step st c i') eqn:Heqr1.
         { (* r1 = Some s *)
           apply E_WhileTrue with s. rewrite Heqr.
           reflexivity.
           apply IHi'. rewrite Heqr1. reflexivity.
           apply IHi'. simpl in H1. assumption. }
         { (* r1 = None *) discriminate H1. }
        * (* r = false *)
          injection H1 as H2. rewrite <- H2.
          apply E_WhileFalse. apply Heqr. Qed.
```

​#剩余习题未完成#​

## 再论求值的确定性

根据关系求值和计步求值的定义等价这一事实， 我们可以给出一种取巧的方式来证明求值*'关系'*是确定性的。

```coq
Theorem ceval_deterministic' : forall c st st1 st2,
     st =[ c ]=> st1 ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 He1 He2.
  apply ceval__ceval_step in He1.
  apply ceval__ceval_step in He2.
  inversion He1 as [i1 E1].
  inversion He2 as [i2 E2].
  apply ceval_step_more with (i2 := i1 + i2) in E1.
  apply ceval_step_more with (i2 := i1 + i2) in E2.
  rewrite E1 in E2. inversion E2. reflexivity.
  omega. omega.  Qed.
```
