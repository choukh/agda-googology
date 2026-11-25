# B8N · 冻结第 1 层初始状态，对照同一个参照链点

请独立审查第八批的冻结对照。工作目录为 agda-googology 仓库根，全程中文，模型 Opus 5.5。先读根目录 `AGENTS.md` 和 `probes/Survey/EBOHandbook.md` §4。协调者会给出本批实验目录 `B8_RUN`。若单独收到本简报，先运行[协调简报的公共准备段](00-协调简报.md)，再执行本路。只在 `$B8_RUN/B8N` 写源码与日志，新模块前缀 `B8Freeze`。

## 要判别的命题

构造路比较更新一次的实际 W4 树。本路把**参照固定在同一个 `Y 1`**，把 W4 的第 1 层树固定为初态 `chainW 0`。在公共模块 `YiLAB7Replay` 上尝试其一：

```agda
frozen : Frozen
-- Frozen = Match (Y 1) (chainW 0)
-- 或
no-frozen : Frozen → ⊥
```

`Y n` 来自 Level 的 `ψ⁰ (Ω₂ + Ω₂)` 的实际链，`double-shape` 给出来源。`chainW 0` 是 W4 第 1 层标准 Ω 树。`seed` 已给出 `Match (Y 0) (chainW 0)`。`Match X y` 要**存在**共同的 d、e，满足 W4 的 `SumR y d`、`Real y e` 以及 Level 的 `Ld X d`、`Lx X e`。排除某一对候选描述只否定那个候选。两种消费者 `consume` 与 `consume-exp` 都接受任意完整见证。[公共接口和消费者](../指令-01.md) · [第七批的反例候选 C1、C4](../../Reports-2026-11-16/attachments/B7A-WK-paper.txt)

## 做法与止损

1. 先试肯定。展开 `Y 1`；在冻结的标准 Ω 树上复用 `seed`、`WSW4.Lem.W1` 的指数证据以及 `WSLevel` 的加法、移位、放宽律。给出允许共享的 d、e，检查比较方向。若有 `frozen`，提交完整见证，以及代入两个消费者得到的闭不等式。这个结果本身即有信息。
2. 再试否定。先写出冻结后某一个消费者的精确左右端，尝试证明该不等式推出空类型，或以已有的不相容定理和反向严格界推出矛盾。示意证明为 `no-frozen m = refute (consume-exp m)`，其中 `refute` 须独立编译，且目标与消费者逐字对上。若用被加项消费者，按其签名做同样检查。也可从接口字段直接得到矛盾，但须覆盖所有允许的 d、e。核对严格关系与值前序的联系；观察到两个头构造、两个影子或两条计算路径不同并不足以否定值界。
3. 若问题在相同编号的配对，且有具体依据，可尝试 `First → ⊥`，或交一个经编译的其他配对下标的见证。保留 `Frozen` 自身的准确状态。两种写法用尽或新代码约到 1200 行即停。若两边都未判定，报最后可编译的实例、卡在哪个不等式及为何现有引理用不上。

## 编译与回报

按仓库约定使用 `--safe --without-K`，沿用公共源码 OPTIONS。第 4 层允许以排中律或函数外延为模块参数；用到时说明哪一步需要它，结论标“条件”。W4、公共接口、旧的证明和仓库文件只读。每次一个 Agda 进程，6G 堆，日志落在本路目录。以下示例假设入口叫 `B8FreezeMain`，在仓库根执行，按实际模块名替换。

```sh
agda +RTS -M6G -RTS --library-file="$B8_RUN/libraries" -i src -i probes -i "$B8_RUN/B8Common" -i "$B8_RUN/B8N" "$B8_RUN/B8N/B8FreezeMain.agda" > "$B8_RUN/B8N/compile.log" 2>&1
code=$?
echo "agda exit $code"
```

回报先写 `Frozen` 的状态，再列新模块、精确签名、前提及实例、退出码、消费者与否定的量化范围。分别标编译定理、有限测试和判断。某次证明受阻就写“未证”。本路只裁定实际覆盖的比较，整体路线的判断交主审。将源码和原文交协调者复核，无须等待构造路。
