# 归纳-递归块: 哪些写法过得了, 哪些过不了 (正性与停机的实测)

> 不含记号. 结论写在 [LvIR](LvIR.lagda.md). 下面 `agda` 块是编译过的; `text` 块是**实测的报错原文**, 对应的文件是临时文件 (`P1`–`P12`), 不进仓库. 报错不是定理: 它说的是 Agda 的检查器, 不是数学上的不可能.
>
> **结论.**
>
> 1. **`Lv` 这个名字不能出现在好输入的定义里, 哪怕在负位置** (`P1`: $\forall i{:}\mathrm{Lv}$; `P2`: $\Sigma\,\ell{:}\mathrm{Lv}$). 所以第 0 层的好输入不能写成 "落在某个层号的折叠之下".
> 2. **归纳的 `Good` 带着自己的数据过不了** (`P3`, 带层号的字段). 这是任务里 "数据型 Good" 那个备选的回答.
> 3. **观测不能是数据类型** (`P4`, `P5`). 哪怕用非一致参数, 字段里没有 `Lv`: 只要字段提到 `Pre` 或 `Ord`, 就经 `Gd` 回到自己的负位置. [InaccThetaObs](InaccThetaObs.lagda.md) 的 `Obs` 不能照搬进块. 观测写成对燃料的**函数**就过了 (`Fuel`). 这一条说明: **归纳-递归让观测前序更难写, 不是更容易.**
> 4. **第 0 层的树不能是 `Tree`** (第一版). `ZN` 的签名里的 `Inp zero` 把 `zero` 这个不变小的参数送回 `Gd`, 停机失败. 改成 `Ord zero = O₀` 就过了 ([LvIRBlock](LvIRBlock.lagda.md)).
> 5. **自界的族能写下来** (`SelfBound`, 编译过). `Good zero y = y ≺⁰ selfC`, `selfC` 是同一个块里折叠的输出. 它不提 `Lv`, 也躲开了 `no-read`. 这是唯一看上去能在块内给出有公共上界的族的写法.
> 6. **但比较或证书一读自界的上界, 停机就失败** (`P11`, `P12`). 第一种: `clo → hsC → vHS → clo`. 第二种 (证书放在输入上): `val → prf → val`. 第三种 (按塔高编号的族, 输入带编号与有限证书, 脊的步进是字面的头一项, `P13`, 这个文件带了两个假设, 只测形状): `term → val → prf → term`. 这是决定性的一处, 三个相邻的设计败在同一个点: **链点属于族的证据要提上界, 上界要链点.** 按任务的约定, 这里停下, 不再修补.
> 7. **每个节点自带输入谓词** (`P7`, `Lv : Set₁`) 的写法能写下来, 但谓词 `Ord k → Set` 里量化不了 `Lv` (宇宙层次报错), 所以它同样不能说 "落在某个层号之下". 节点谓词可以提**固定的**目标, 所以它躲开 `no-read`; 代价是链的拥有者要证下一点满足谓词, 这就是把比较问题搬到了链上 (判断, 没有证).

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.LvIRPos where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.LvIRBase
```

## §1 好输入里提 `Lv`

```text
P1: Gd k t = (i : Lv) → Ord i → ⊤
error: [NotStrictlyPositive]
Lv is not strictly positive, because it occurs
to the left of an arrow
in the first clause
in the definition of Gd, which occurs
                       in the 4th argument of Σ
                       to the left of an arrow
                       in the type of the constructor limᴼ
                       in the definition of Lv.

P2: Gd k t = Σ Lv λ ℓ → Ord ℓ
error: [NotStrictlyPositive]
Lv is not strictly positive, because it occurs
in the third argument of Σ
in the first clause
in the definition of Gd, which occurs
                       in the 4th argument of Σ
                       to the left of an arrow
                       in the type of the constructor limᴼ
                       in the definition of Lv.
```

## §2 数据型的 `Good` 与观测

```text
P3: data Reach : (k : Lv) → Ord k → Set where
      rz  : ∀ {k} → Reach k zero
      rψ₀ : (ℓ : Lv) → Ord ℓ → Reach zero zero
error: [NotStrictlyPositive]
Lv is not strictly positive, because it occurs
in the type of the constructor rz
in the definition of Reach, which occurs
                          in the 4th argument of Σ
                          to the left of an arrow
                          in the type of the constructor limᴼ
                          in the definition of Lv.

P4: data Ctx (k : Lv) : Set where
      top  : Ctx k
      psi  : (r : Pre k) → Ctx (at k r) → Ctx k
      addc : Ord k → Ctx k → Ctx k
    Gd k t = Ctx k → ⊤
error: [NotStrictlyPositive]
Ctx is not strictly positive, because it occurs
to the left of an arrow
in the first clause
in the definition of Gd, which occurs
                       in the 4th argument of Σ
                       in the third argument of Σ
                       in the 4th argument of _⊎_
                       in the second clause
                       in the definition of Pre, which occurs
                                               in the type of the constructor psi
                                               in the definition of Ctx.

P5: data Ctx (k : Lv) : Set where
      top  : Ctx k
      addo : (l : Lv) → Ord l → Ctx l → Ctx k
    Gd k t = Ctx k → ⊤
error: [NotStrictlyPositive]
Ctx is not strictly positive, because it occurs
to the left of an arrow
in the first clause
in the definition of Gd, which occurs
                       in the 4th argument of Σ
                       to the left of an arrow
                       in the type of the constructor limᴼ
                       in the definition of Lv, which occurs
                                              in the type of the constructor addo
                                              in the definition of Ctx.
```

对燃料的函数过了. 下面是最小形式: 观测的上下文不是数据, 是 `ℕ` 上的递归; 它不提 `Lv`.

```agda
module Fuel where
  data Tree (P : Set) (Br : P → Set) : Set where
    zero : Tree P Br
    limᵢ : (r : P) → (Br r → Tree P Br) → Tree P Br

  data Lv : Set
  Pre  : Lv → Set
  Low  : (ℓ : Lv) → Pre ℓ → Set
  Ord  : Lv → Set
  Gd   : (k : Lv) → Ord k → Set
  Ctx  : ℕ → (K : Lv) → Set

  data Lv where
    zero : Lv
    limᴼ : (k : Lv) → (Σ (Ord k) (Gd k) → Lv) → Lv

  Pre zero = ⊥
  Pre (limᴼ k g) = ⊤ ⊎ Σ (Σ (Ord k) (Gd k)) λ x → Pre (g x)
  Low (limᴼ k g) (inj₁ _) = Σ (Ord k) (Gd k)
  Low (limᴼ k g) (inj₂ (x , r)) = Low (g x) r
  Ord ℓ = Tree (Pre ℓ) (Low ℓ)

  Ctx zero K = ⊤
  Ctx (suc d) K = (Ord K × Ctx d K) ⊎ ⊤

  Gd k t = (d : ℕ) → Ctx d k → ⊤
```

## §3 第 0 层是 `Tree` 的第一版

```text
error: [TerminationIssue]
Termination checking failed for the following functions:
  Inp, Gd, Good, NodeG, ZN
Problematic calls:
  Inp zero
  Gd k
  Good (limᴼ k g) z
  NodeG k k r f
  ZN K f
```

`ZN K f` 的签名提 `Inp zero`, 而 `Inp` 调 `Gd`, 参数 `zero` 不比模式小. 签名上的调用也算. 这和 [EBOTopIR](EBOTopIR.lagda.md) 记录的 `Ordᴸ (at k r)` 是同一类问题.

## §4 自界的族

第 0 层的好输入是一个闭树 `selfC` 的前驱, 而 `selfC` 是块里折叠的输出. **这个块过了.** 它的目的是回答 "能不能在块内给出一个有公共上界的族": 形状上能. `Good zero` 不提 `Lv`, 所以正性不挡. 反例族不在里面 (没有理由认为 $y_s\prec$ `selfC`), 所以 `no-read` 不挡.

```agda
module SelfBound where
  data Tree (P : Set) (Br : P → Set) (Dr : Set) : Set where
    zero : Tree P Br Dr
    limᵢ : (r : P) → (Br r → Tree P Br Dr) → Tree P Br Dr
    up   : Dr → Tree P Br Dr

  data Lv : Set
  Pre  : Lv → Set
  Low  : (ℓ : Lv) → Pre ℓ → Set
  DnT  : Lv → Set
  Ord  : Lv → Set
  Good : (k : Lv) → Ord k → Set
  fold : (k : Lv) (t : Ord k) → Good k t → O₀
  selfC : O₀

  data Lv where
    zero : Lv
    limᴼ : (k : Lv) → (Σ (Ord k) (Good k) → Lv) → Lv

  Pre zero = ⊥
  Pre (limᴼ k g) = ⊤ ⊎ Σ (Σ (Ord k) (Good k)) λ x → Pre (g x)
  Low (limᴼ k g) (inj₁ _) = Σ (Ord k) (Good k)
  Low (limᴼ k g) (inj₂ (x , r)) = Low (g x) r
  DnT zero = ⊥
  DnT (limᴼ k g) = Ord k
  Ord zero = O₀
  Ord (limᴼ k g) = Tree (Pre (limᴼ k g)) (Low (limᴼ k g)) (DnT (limᴼ k g))

  Good zero y = y ≺⁰ selfC
  Good (limᴼ k g) zero = ⊤
  Good (limᴼ k g) (limᵢ r f) = ⊥
  Good (limᴼ k g) (up x) = Good k x

  fold zero y g = y
  fold (limᴼ k h) zero g = O₀.zero
  fold (limᴼ k h) (up x) g = fold k x g

  selfC = fold (limᴼ zero (λ _ → zero)) zero tt
```

## §5 自界的族一读上界就失败

两个相邻的设计, 都把**链的下一点**放进族里. 块的其余部分与 §4 相同, 这里只写新增的定义. `selfC` 是链的极限, 比较读上界的证书 `hsC`.

```text
P11 (比较与 HS 都读 hsC):
  selfC = lim (λ n → suc (val n))
  val (suc n) = fold zero (val n) (prf n)
  prf n = ≺l n (≺z (≅⁰-refl _))
  vHS (suc n) = clo zero (val n) (prf n)
  clo zero y g = hsPick (cmp g g hsC) (hsPred g hsC)
  hsC = hl (λ n → hs (vHS n)) st
error: [TerminationIssue]
Termination checking failed for the following functions:
  clo, vHS, hsC
Problematic calls:
  hsC
  clo zero (val n) (prf n)
  vHS n

P12 (证书放在输入上: Good zero y = (y ≺⁰ selfC) × HS y, 只有比较读 hsC):
  val (suc n) = fold zero (val n) (prf n , vHS n)
error: [TerminationIssue]
Termination checking failed for the following functions:
  val, prf
Problematic calls:
  val n
  prf n
```

第三种, 族按塔高编号, 输入带编号与有限证书: `G y = Σ m. (y ≺⁰ x m) × Cert⁻ m × HS y`, 证书只到第 $m-1$ 步, 脊的步进 `stx` 是字面的头一项. 第一个循环 (`cert → stx → term → val → cert⁻`) 用 `--termination-depth=3` 消掉了. 剩下的是:

```text
P13:
  x n = lim (term n)
  term n j = val n j
  val n (suc j) = br (val n j , n , prf n j , cert⁻ n , vhs n j)
  prf n j = ≺l (suc j) (≺Pick (readC n (cert⁻ n)) (strict (vhs n j)))
error: [TerminationIssue]
Termination checking failed for the following functions:
  T.term, T.val, T.prf
Problematic calls:
  term n
  val n j
  prf n j
```

`prf n j` 的隐式参数是 `x n` 的基本列 `term n`, 而 `term n` 对任意下标调用 `val`. 所以 $j$ 不降.

(`SelfBound` 的前身 `P8` 也有 `val → prf`, 那里过了, 原因我没有查清: 那个版本的分支不读 `Cert`, 比较没有进来. 所以我不声称 "凡是提上界就过不了", 只声称上面三个读证书的版本过不了.)

**这不只是检查器的保守 (判断).** `prf n` 的类型提 `selfC`, `selfC` 是全部 `val m` 的极限. 真实的情形比玩具更糟: 好输入 $y\prec x_{100}$ 进入 $x_3$ 的节点的分支, 而 `Good` 的节点要对**全部**好输入成立. 那么 $x_3$ 的 `Good` 要比较 $y$ 与 $x_3$ 里的目标, 比较要 $x_3\sqsubseteq x_{100}$, 这要 $x_{100}$ 的证书, 它又要 $x_3$ 的. 按塔高分层就断开这个循环, 那就是 `LevelK*` 与 `LvStrat*` 在做的事, 不再是归纳-递归.

## §6 节点自带谓词

能写下来 (`P7`), `Lv : Set₁`, `limᵢ : (r : P) (Q : Br r → Set) → (Σ (Br r) Q → Tree) → Tree`. 量化 `Lv` 过不了:

```text
Bad : Ord zero → Set
Bad t = Σ Lv (λ ℓ → Ord ℓ)
error: [UnequalSorts]
Set₁ != Set
when checking that the expression Σ Lv (λ ℓ → Ord ℓ) has type Set
```

所以节点谓词只能提固定的东西. 穿透的输出节点取 $Q\,v$ = "$v$ 的前驱对目标 $\omega+1$ 有判决", `no-read` 就不挡了, 因为 $Q$ 不含反例族. 但每一个走到这个节点的链的拥有者都要证 $Q$ 对下一点成立: 下一点的前驱与 $\omega+1$ 比. 这要字面的公共上界, 也就是下一点确实字面含 $\omega+1$. 我没有证这个, 也没有写这个设计.
