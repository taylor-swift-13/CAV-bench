---
name: verify
description: Verify skill，消费 Contract 输出完成注解、证明和编译检查。
---

Verify 在 QCP C 程序上完成 annotation + proof + compile，不修改 function contract。
这里的 function contract 只指函数级 `Require` / `Ensure` 前后条件；loop invariant、`Assert`、`Inv Assert`、`which implies` 和 `where` 属于 verification annotation。

本 skill 自包含 Verify 阶段需要遵守的 CAV 规则。QCP skill 文档只在缺少具体语法、tactic 或 final-check 细节时按需最小读取，不能替代同型 C/annotation/proof 示例。

## 0. 职责

- Agent 直接在 QCP 根目录启动，在当前 QCP mirror scratch 内工作。
- 先读取 runner prompt、本 skill 和当前 QCP mirror 内容；不要启动时批量读取 QCP skill 或整个 `docs/` 目录。
- 唯一文字产物是当前 QCP mirror logs 中的 `issues.md` 和 `metrics.md`。
- 不写过程 reasoning 日志。

## 1. 路径和读写边界

路径：

- 输入：`input/<dataset>/<name>.c`、可选 `input/<dataset>/<name>.v`。
- Workspace：`output/verify_<timestamp>_<name>/`，runner-owned artifact collection。
- QCP C/header mirror：`QualifiedCProgramming/QCP_examples/CAV/<workspace>/`
- QCP Coq mirror：`QualifiedCProgramming/SeparationLogic/examples/CAV/<workspace>/`
- 原始 `.v` bare import deps：`QualifiedCProgramming/SeparationLogic/examples/CAV/<workspace>/deps/`
- QCP mirror logs：`QualifiedCProgramming/SeparationLogic/examples/CAV/<workspace>/logs/`

规则：

- 只读本 verify skill、runner prompt、本 skill 允许的官方示例/教程目录，以及当前 workspace 对应的 QCP mirror C/header、Coq、original spec deps 和 mirror logs；确实需要 QCP 语法、tactic 或 final-check 细节时，才最小读取 §2 列出的相关 QCP skill 文档。
- 只写当前 workspace 对应的 QCP mirror C/header、Coq 目录中除 `deps/` 外的文件，以及 mirror logs 中的 `issues.md` / `metrics.md`。
- 禁止修改 `output/`、repo-level `annotated/`、`input/`、原始 function contract、原始 C 实现、`scripts/`、repo-level `skills/`、QCP 源码或其它 workspace。
- 禁止读取 `output/`、repo-level `annotated/`、`input/`、`scripts/`、自己的 `agent_stdout_*.jsonl`、`git log` / `git show`。除官方示例/教程目录和当前 workspace 外，禁止读取其它 QCP mirror workspace。
- 禁止修改 `QualifiedCProgramming/SeparationLogic/examples/CAV/<workspace>/deps/` 中 staged 原始 `.v` 规格；若原始规格错误，只能走 `contract_program_mismatch_blocker`。

## 2. 资料读取

Runner prompt 提供当前 case 的 QCP mirror 路径、QCP final-check 摘要和 CAV 边界。本 skill 和当前 runner prompt 是 CAV 侧规则来源。

- 进入 annotation/proof 修改前，必须按本 skill 检索并读取具体相关示例：
  - C/annotation 示例来自 `QCP_examples/{Applications_human,LLM_bench,QCP_demos_human,QCP_demos_LLM,stdlib}/`；
  - 对应证明来自 `SeparationLogic/examples/{Applications_human,LLM_bench,QCP_demos_human,QCP_demos_LLM}/` 和 `SeparationLogic/stdlib/`；
  - 相关教程来自 `tutorial/`；
  - CAV 历史同型 workspace 只能作为补充参考，不能替代上述官方示例源。
- QCP skill 文档路径只作为可选参考，不要求启动时读取；annotation 语法、symexec 报错、proof tactic、final-check 细节不确定时，只读取一个最相关的小文件或章节：
  - orchestration：`QualifiedCProgramming/.agents/skills/verification-orchestrator/SKILL.md`
  - annotation filling：`QualifiedCProgramming/.agents/skills/annotation-filling/SKILL.md`
  - annotation checking：`QualifiedCProgramming/.agents/skills/annotation-checking/SKILL.md`
  - VC checking：`QualifiedCProgramming/.agents/skills/vc-checking/SKILL.md`
  - group proof：`QualifiedCProgramming/.agents/skills/group-worker-proving/SKILL.md`
  - final check：`QualifiedCProgramming/.agents/skills/final-check/SKILL.md`
  - 常用细节文档：`QualifiedCProgramming/.agents/skills/annotation-filling/docs/annotation-guide.md`、`QualifiedCProgramming/.agents/skills/annotation-filling/docs/pure-proposition-predicates.md`、`QualifiedCProgramming/.agents/skills/annotation-filling/docs/array-string-guide.md`、`QualifiedCProgramming/.agents/skills/group-worker-proving/docs/refinement-proof-tactics.md`、`QualifiedCProgramming/.agents/skills/group-worker-proving/docs/separation-logic-whole-proof-tactics.md`、`QualifiedCProgramming/.agents/skills/final-check/docs/final-check-guide.md`
- 示例检索必须围绕当前失败点和题型关键词；实际读取的示例路径要记录到 `logs/issues.md` 或 `logs/metrics.md`。
- 按 runner prompt 给出的 QCP 阶段摘要推进 annotation、symexec、proof、final-check。
- 以 runner prompt 给出的命令和 QCP final-check 顺序作为端到端编排入口。
- 禁止用泛搜库源码或无关 demos 代替当前失败点驱动的 annotation/proof 修补。

## 3. Verify 主循环

1. 修改 annotation。
2. 运行 symexec 生成 VC。
3. 若 symexec 失败或 VC 缺 annotation 中间事实，回到 annotation 修改。
4. 进入 proof 阶段后，补当前 QCP Coq mirror 中的 `<name>_proof_manual.v`。
5. 若 proof 暴露 annotation 缺口，回到 annotation 阶段并重跑 symexec。
6. 当前 proof 和 runner 最终验收要求都满足后才退出。

- Annotation 只新增或修改验证注解，不修改原始 C 实现。
- 公共验证头使用裸名 include，并保持原名：
  ```c
  #include "verification_stdlib.h"
  #include "verification_list.h"
  #include "int_array_def.h"
  #include "char_array_def.h"
  ```
- Annotation 变更后重跑 symexec。
- 重跑 symexec 前保存当前 generated `.v` 到当前 QCP mirror 的 `.tmp/` 或 runner prompt 指定位置，并复用旧 proof 结构。
- 禁止手改 `*_goal.v`、`*_proof_auto.v`、`*_goal_check.v`；这些文件只能由 symexec 生成。
- Target `.v` 中只允许编辑 `<name>_proof_manual.v`，且只允许把 QCP 留下的 `Admitted` 证明洞替换成真实 proof；不能为了通过检查去改 manual 中的 statement/import，也不能改其它三个 target `.v`。
- 只改 `proof_manual.v` 时不重跑 symexec。
- 禁止证明或编辑 `proof_auto.v`；它是 QCP 自动生成的证明产物，手工证明负担只在 `proof_manual.v`。
- `proof_manual.v` 中所有未完成手工义务必须用真实证明完成，不得留下占位、假设、绕过或伪造证明。
- 禁止改 VC 目标或导入绕过性结论。
- 禁止因普通 proof obligation、单个 theorem、tactic 失败、缺 lemma、耗时或模型不会证而退出。
- 退出前当前 QCP mirror 中必须有当前已填写的 `<name>_proof_manual.v`。

命令模板如下；实际 `<workspace>`、`<name>`、`<annotated>.c` 和 deps 列表以 runner prompt 的当前 case 路径为准。

从 `QualifiedCProgramming/` 根目录运行 symexec：

```bash
linux-binary/symexec \
  --goal-file=SeparationLogic/examples/CAV/<workspace>/<name>_goal.v \
  --proof-auto-file=SeparationLogic/examples/CAV/<workspace>/<name>_proof_auto.v \
  --proof-manual-file=SeparationLogic/examples/CAV/<workspace>/<name>_proof_manual.v \
  --coq-logic-path=SimpleC.EE.CAV.<workspace> \
  -IQCP_examples/stdlib/ \
  -slp QCP_examples/stdlib/ SimpleC.StdLib \
  -IQCP_examples/QCP_demos_LLM/ \
  -slp QCP_examples/QCP_demos_LLM/ SimpleC.EE.QCP_demos_LLM \
  --input-file=QCP_examples/CAV/<workspace>/<annotated>.c \
  --no-exec-info
```

从 `QualifiedCProgramming/` 根目录按依赖顺序编译 Coq，不并行跳步：

```bash
cd SeparationLogic && coqc \
  -Q examples/CAV/<workspace>/deps "" \
  -R flocq/src Flocq \
  -R SeparationLogic SimpleC.SL \
  -R unifysl Logic \
  -R sets SetsClass \
  -R compcert_lib compcert.lib \
  -R auxlibs AUXLib \
  -R examples SimpleC.EE \
  -R stdlib SimpleC.StdLib \
  -R StrategyLib SimpleC.StrategyLib \
  -R Common SimpleC.Common \
  -R fixedpoints FP \
  -R MonadLib MonadLib \
  -R listlib ListLib \
  -R MaxMinLib MaxMinLib \
  -R GraphLib GraphLib \
  -R SumLib SumLib \
  -R tracelib TraceLib \
  -R coq-record-update/src RecordUpdate \
  -Q algorithms Algorithms \
  examples/CAV/<workspace>/deps/<dep>.v

cd SeparationLogic && coqc <same load-path args> examples/CAV/<workspace>/<name>_goal.v
cd SeparationLogic && coqc <same load-path args> examples/CAV/<workspace>/<name>_proof_auto.v
cd SeparationLogic && coqc <same load-path args> examples/CAV/<workspace>/<name>_proof_manual.v
cd SeparationLogic && coqc <same load-path args> examples/CAV/<workspace>/<name>_goal_check.v
```

若有多个原始 bare-import deps，先把每个 `examples/CAV/<workspace>/deps/<dep>.v` 按 runner 给出的 dependency closure 顺序全部编译完，再编译四个 target `.v`。只修改 `proof_manual.v` 后，可以从 `proof_manual.v` 重新编译到 `goal_check.v`；annotation 改动后必须重新运行 symexec 并重新走完整编译顺序。

## 4. Audit、编译和退出

正式成功判定只使用 runner 对当前 QCP mirror 的最终验收。

1. annotated C 和公共头位于 `QualifiedCProgramming/QCP_examples/CAV/<workspace>/`。
2. target Coq 文件位于 `QualifiedCProgramming/SeparationLogic/examples/CAV/<workspace>/`。
3. 原始 `.v` bare-import 依赖闭包位于 `QualifiedCProgramming/SeparationLogic/examples/CAV/<workspace>/deps/`。
4. symexec 使用 `--coq-logic-path=SimpleC.EE.CAV.<workspace>`。
5. QCP final-check 编译顺序是：
   `original deps -> goal -> proof_auto -> proof_manual -> goal_check`。
6. Runner 从 QCP mirror 收集 annotated C、`logs/issues.md`、`logs/metrics.md` 和最终四个 `.v`。

- 所有 symexec、coqc、final-check 都在当前 QCP mirror scratch 中完成。
- 以 runner 提供的当前 QCP mirror final-check 要求作为最终检查标准。
- 禁止 agent 复制产物；runner 负责复制回 output，且不复制 `.vo/.glob/.aux`。
- final-check 或 runner 验收要求尚未满足时不要退出；继续编辑 annotation/proof 并再次运行相关 QCP 检查。
- 禁止任何第三种最终状态。
- 普通 annotation、symexec、coqc、proof 失败都不是退出理由。

## 5. 日志和最终结果

- `logs/issues.md` 记录真正遇到的 issue：现象、定位、关键报错片段、最终解决方式或卡住原因。
- `logs/metrics.md` 记录最终结果、attempt、耗时、agent/model、输入/输出路径和 runner 最终验收结果。
- 当前 QCP mirror 满足 final-check 和 runner 最终验收要求后，维护 `logs/issues.md` 和 `logs/metrics.md`，最后一行写裸的 `Final Result: Success`。
- final-check 或 runner 验收要求尚未满足时可以持续更新 `logs/issues.md`，但更新后继续工作。
- 写完 `issues.md` 或 `metrics.md` 不是退出理由；final-check 或 runner 验收要求尚未满足就继续。
- 只有确认 `contract_program_mismatch_blocker` 时，最后一行才写裸的 `Final Result: Fail`。
- `contract_program_mismatch_blocker` 指 Contract 与原始程序语义冲突，当前 case 必须回 Contract 阶段或用户决策，且无法通过 annotation/proof 修复。
- 写 `Final Result: Fail` 时，`logs/issues.md` 必须包含 `contract_program_mismatch_blocker`：失败 gate、退出码或 theorem/witness 名、关键报错、相关路径、Contract 与程序语义哪里冲突、为什么无法通过 annotation/proof 修复且必须回 Contract/用户决策。
- 禁止在 mirror logs 下写 probe 文件、proof 备份或临时 Coq 文件；logs 只放 `issues.md` 和 `metrics.md`，临时 probe/备份放当前 Coq mirror 的 `.tmp/`。

## 6. proof-only

`Mode: proof-only` 标记触发时，读取 `MODE_PROOF_ONLY.md`。该模式适用于 symexec 已跑过、仅补 `proof_manual.v` 的子场景；若 proof 暴露 annotation 缺口，按本文工作循环回到 annotation/symexec。

规则：

- proof-only 模式下只补 `proof_manual.v` 和运行 proof/final-check 相关检查。
- 若 proof-only 暴露 annotation 缺口，回到 annotation/symexec 工作循环。
