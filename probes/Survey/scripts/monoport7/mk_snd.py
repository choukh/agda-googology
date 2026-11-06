# 生成 MonoPort7Snd: 节点一步与归纳对一切不含 Ω-极限的层 (hs 与 hl).
# 前半 (SemK 到 Node) 在本脚本里手写; sndS 的子句从 MonoPort6Snd 逐字取出, 只换 ni 那一句 (节点从 ss Pk 换成任意 r).
# 用法: python3 mk_snd.py <仓库根>
import sys, os
root = sys.argv[1]
src = open(os.path.join(root, 'probes/OCF/Align/MonoPort6Snd.lagda.md')).read()
code = src[src.index('```agda'):]
a = code.index("sndS b fb ac ll RelM.n0⊑")
b = code.index("```", a)
cl = code[a:b]
old_ni = cl[cl.index("sndS b fb (acc f) ll (RelM.ni⊑"):cl.index("sndS b fb ac ll (RelM.nwˡ h)")]
new_ni = '''sndS b fb (acc f) ll (RelM.ni⊑ {k = k} r {u = u} {u′ = u′} mu mu′ cr) Aᵢ Aⱼ hi hj hij tt tt w w′ c c′ Y Y′ (L.K.cx cw) g g′ s cb =
  obs cb (Node.step b fb f ll r u u′ (sndArg k (finS r fb) (f r)) mu mu′ cr
            (λ z z′ l → sndS b fb (acc f) (⊲ᴴ↑ C.self ll) (mu z z′ l))
            (λ z z′ l → sndS b fb (acc f) (⊲ᴴ↑ C.self ll) (mu′ z z′ l))
            (λ z z′ l → sndS b fb (acc f) (⊲ᴴ↑ C.self ll) (cr z z′ l))
            Aᵢ Aⱼ hi hj hij w w′ Y Y′ cw g g′ s)
'''
assert old_ni in cl
cl = cl.replace(old_ni, new_ni)
# 前半: 取 MonoPort6Snd 的 toHA₀ 之前的部分作模板, 其余手写
pre = code[:code.index("SemK : ")]
pre = pre.replace('module OCF.Align.MonoPort6Snd', 'module OCF.Align.MonoPort7Snd')
pre = pre.replace('open import OCF.Align.HtFeedTree using (hs; hl; hΩ; ss; sl; sL; StH; Vs; D; AccY; acc; mkOf; inS; outS; ⊲ᴴ↑;',
                  'open import OCF.Align.HtFeedTree using (hs; hl; hΩ; ss; sl; sL; StH; Vs; D; AccY; acc; mkOf; inS; outS; ⊲ᴴ↑; NZ-S;')
pre = pre.replace('open import OCF.Align.MonoPort6Rel Λ lΛ lW t₀', 'open import OCF.Align.MonoPort7Rel Λ lΛ lW t₀')
pre = pre.replace('open import OCF.Align.MonoPort6Int Λ lΛ lW t₀ using (IntMK; cx00; module CxS)',
                  'open import OCF.Align.MonoPort7Int Λ lΛ lW t₀ using (IntMK; cx00; module CxS; cxLN; cxRN; finS; toN; fromN)')
pre = pre.replace('open import OCF.Align.MonoPort6Lay Λ lΛ lW t₀ using (module L)', 'open import OCF.Align.MonoPort7Lay Λ lΛ lW t₀ using (module L; HAKN)')
pre = pre.replace('(对层分两种: 第 0 层与 `hs b`)', '(对层分三种: 第 0 层, `hs b`, `hl f`)')
mid = open(os.path.join(root, 'probes/Survey/scripts/monoport7/snd_mid.txt')).read()
hdr = open(os.path.join(root, 'probes/Survey/scripts/monoport7/snd_header.md')).read()
open(os.path.join(root, 'probes/OCF/Align/MonoPort7Snd.lagda.md'), 'w').write(hdr + pre + mid + cl + '```\n')
