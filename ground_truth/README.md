# DLC HumanEval Ground Truth 标准

`ground_truth/<problem>` 是最终可重放的证明库，不是中间导入缓存。目录存在不等于通过验收；每个 case 必须有独立的成功日志。

## 数据分层

- 更新来源：`/home/yangfp/QualifiedCProgramming/QCP_examples/humaneval/multi_dimensional_arrays`。
- `input/humaneval` 只保留程序、函数 contract、`Extern Coq` / `Import Coq` 和必要接口；不得包含循环 invariant、内部 `Assert`、`where` hint 或证明。
- `annotated_input/humaneval` 的 C 文件保留完整 annotation，但对应 `.v` 仍不得暴露 helper lemma 或证明。
- 完整 annotation、case-local support、生成的 VC 和人工证明只保留在 `ground_truth/<problem>`。
- 使用 DLC 固定的 `QualifiedCProgramming` 子模块；可以迁移 case-local 证明代码，不能迁移外部 QCP 库改动。

## 迁移规则

- 文件统一使用真实题名 `pNNN_name`，不保留 `coins_N` / `C_N` 模块名。
- 必要但不属于 DLC 固定 QCP 库的定义必须放在 case-local `<problem>.v` 中。例如 p007 的 `substring_at` / `strstr_result`。
- `proof_manual.v` 不允许出现 `Admitted`、`admit`、`Abort` 或自造 `Axiom`。
- `goal.v`、`proof_auto.v`、`goal_check.v` 必须由当前 DLC `symexec` 重新生成；不能把旧生成文件直接当作通过证据。
- 不提交 `.vo`、`.vok`、`.vos`、`.glob`、`.aux`、cache 或旧 `deps/`。

## 验收

在仓库根目录运行：

```bash
COQC='opam exec --switch=qcp-8.20 -- coqc' \
python3 scripts/legacy/verify_ground_truth_humaneval.py \
  --problem pNNN_name
```

验收顺序为 symexec、support、goal、proof_auto、proof_manual、goal_check。成功后，`ground_truth/<problem>/verify_ground_truth.log` 必须包含 5 个 `[OK]`，且不包含 `[FAIL]` 或 `Error:`。

公开输入由下列命令从已验收 ground truth 派生；必须显式指定 case，避免误改其他任务：

```bash
python3 scripts/sanitize_ground_truth_inputs.py --write \
  --problem pNNN_name
```

## 2026-07-12 多维任务更新

已在 DLC 环境中完成 fresh replay 并收录 16 个更新：

- `p001_separate_paren_groups`
- `p007_filter_by_substring`
- `p014_all_prefixes`
- `p028_concatenate`
- `p029_filter_by_prefix`
- `p074_total_match`
- `p101_words_string`
- `p105_by_length`
- `p112_reverse_delete`
- `p113_odd_count`
- `p117_select_words`
- `p147_get_matrix_triples`
- `p149_sorted_list_sum`
- `p153_Strongest_Extension`
- `p158_find_max`
- `p160_do_algebra`

本轮未收录：p012、p087、p095、p115、p129、p148 的源证明仍含未完成项；p125 仍在验证中。仓库中其他既有目录未在本轮重新分类。
