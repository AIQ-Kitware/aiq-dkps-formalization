#!/usr/bin/env python3
"""Build auditable API-equivalent cost and operational-footprint artifacts.

Measured ledger rows are the evidence.  Prices and energy/carbon parameters are
versioned post-hoc assumptions, so improved provider or hardware information can
be substituted without rewriting historical token measurements.
"""

from __future__ import annotations

import csv
import hashlib
import json
import pathlib
import sys
from dataclasses import dataclass

HERE = pathlib.Path(__file__).resolve().parent
DRAFT = HERE
sys.path.insert(0, str(DRAFT / "scripts"))

from accounting_lib import canonical_model_name, latex_escape, load_commits, parse_dt, repo_root

ROOT = repo_root(DRAFT)
GENERATED = DRAFT / "generated"
SNAPSHOTS = DRAFT / "snapshots"
CONFIG = json.loads((DRAFT / "analysis_config.json").read_text())
ASSUMPTIONS_PATH = DRAFT / "resource_valuation_assumptions_20260817.json"
PRICING_PATH = DRAFT / "resource_valuation_model_pricing_20260817.csv"
ACCOUNTING_SUMMARY_PATH = GENERATED / "accounting_summary.json"
ACCOUNTING_MANIFEST_PATH = GENERATED / "commit_accounting_manifest.csv"
PRIMARY_REPOSITORY = CONFIG.get("primary_repository", "aiq-dkps-formalization")
LEDGER_REPOSITORIES = set(CONFIG.get("included_ledger_repositories", {PRIMARY_REPOSITORY: ""}))
EXCLUDED_ONLY_PREFIXES = tuple(CONFIG.get("exclude_commits_if_only_touch", []))
CUTOFF = CONFIG["history_cutoff_commit"]
TOKEN_KEYS = ("input", "cache_write", "cache_read", "output")


@dataclass(frozen=True)
class Interval:
    low: float
    central: float
    high: float

    @classmethod
    def exact(cls, value: float) -> "Interval":
        return cls(float(value), float(value), float(value))

    @classmethod
    def coerce(cls, value) -> "Interval":
        if isinstance(value, cls):
            return value
        if isinstance(value, (int, float)):
            return cls.exact(value)
        if isinstance(value, (list, tuple)) and len(value) == 3:
            return cls(*map(float, value))
        raise ValueError(f"expected scalar or [low, central, high], got {value!r}")

    def __add__(self, other) -> "Interval":
        other = Interval.coerce(other)
        return Interval(self.low + other.low, self.central + other.central, self.high + other.high)

    __radd__ = __add__

    def __mul__(self, other) -> "Interval":
        other = Interval.coerce(other)
        return Interval(self.low * other.low, self.central * other.central, self.high * other.high)

    __rmul__ = __mul__

    def __truediv__(self, other) -> "Interval":
        other = Interval.coerce(other)
        if other.low <= 0:
            raise ValueError("interval divisor must be positive")
        return Interval(self.low / other.high, self.central / other.central, self.high / other.low)


ZERO = Interval.exact(0.0)


def commit_is_excluded(commit) -> bool:
    if not commit.files or not EXCLUDED_ONLY_PREFIXES:
        return False
    return all(any(path.startswith(prefix) for prefix in EXCLUDED_ONLY_PREFIXES) for path in commit.files)


def token_dict(values) -> dict[str, int]:
    vals = (list(values or []) + [0, 0, 0, 0])[:4]
    return dict(zip(TOKEN_KEYS, (int(v or 0) for v in vals)))


def load_prices() -> dict[str, dict]:
    prices = {}
    with PRICING_PATH.open(newline="", encoding="utf-8") as f:
        for row in csv.DictReader(f):
            model = canonical_model_name(row.get("model") or "")
            if model:
                prices[model] = row
    return prices


def price_row(tokens: dict[str, int], price: dict) -> float | None:
    rates = []
    for kind in TOKEN_KEYS:
        value = (price.get(f"{kind}_usd_per_million") or "").strip()
        if not value:
            return None
        rates.append(float(value))
    return sum(tokens[k] * rate * 1e-6 for k, rate in zip(TOKEN_KEYS, rates))


def serving_metrics(tokens: dict[str, int], turns: float, stack: dict, output: Interval | None = None):
    inp = Interval.exact(tokens["input"])
    cw = Interval.exact(tokens["cache_write"])
    cr = Interval.exact(tokens["cache_read"])
    out = output or Interval.exact(tokens["output"])
    effective_input = (
        inp
        + cw * Interval.coerce(stack["cache_write_work_factor"])
        + cr * Interval.coerce(stack["cache_read_work_factor"])
    )
    seconds = (
        effective_input / Interval.coerce(stack["prefill_tokens_per_second"])
        + out / Interval.coerce(stack["decode_tokens_per_second"])
        + Interval.exact(turns) * Interval.coerce(stack["fixed_seconds_per_turn"])
    )
    energy = (
        seconds
        * Interval.coerce(stack["server_power_kw"])
        * (1.0 / 3600.0)
        * Interval.coerce(stack["pue"])
    )
    carbon = energy * Interval.coerce(stack["grid_gco2e_per_kwh"])
    return seconds, energy, carbon


def add_metric(stat: dict, key: str, value: Interval) -> None:
    stat[key] = stat.get(key, ZERO) + value


def fmt_usd(value: float) -> str:
    return f"{value:,.0f}"


def fmt_one(value: float) -> str:
    return f"{value:,.1f}"


def truncated_scientific(value: float) -> str:
    """One leading digit, truncated toward zero, rendered for inline LaTeX."""
    import math
    value = abs(float(value))
    if value == 0:
        return r"\(0\)"
    exponent = math.floor(math.log10(value))
    coefficient = math.floor(value / (10 ** exponent))
    return rf"\({coefficient}\times 10^{{{exponent}}}\)"


def main() -> None:
    GENERATED.mkdir(parents=True, exist_ok=True)
    SNAPSHOTS.mkdir(parents=True, exist_ok=True)
    assumptions = json.loads(ASSUMPTIONS_PATH.read_text())
    accounting_summary = json.loads(ACCOUNTING_SUMMARY_PATH.read_text())
    coverage = accounting_summary["coverage_proxies"]
    with ACCOUNTING_MANIFEST_PATH.open(newline="", encoding="utf-8") as f:
        exact_primary_shas = {
            row["commit"] for row in csv.DictReader(f)
            if row.get("accounting_state") == "exact_measured"
        }
    stack_cfg = assumptions["serving_stack"]
    stack = {
        "pue": stack_cfg["pue"],
        "grid_gco2e_per_kwh": stack_cfg["grid_gco2e_per_kwh"],
        "prefill_tokens_per_second": stack_cfg["prefill_tokens_per_second"],
        "decode_tokens_per_second": stack_cfg["decode_tokens_per_second"],
        "server_power_kw": stack_cfg["server_power_kw"],
        "fixed_seconds_per_turn": stack_cfg["fixed_seconds_per_turn"],
        "cache_write_work_factor": stack_cfg["cache_write_work_factor"],
        "cache_read_work_factor": stack_cfg["cache_read_work_factor"],
    }

    commits = load_commits(ROOT, CUTOFF)
    cutoff_commit = next((c for c in commits if c.commit == CUTOFF), commits[-1])
    cutoff_dt = cutoff_commit.timestamp_dt
    excluded_sha = {c.commit for c in commits if commit_is_excluded(c)}

    stats: dict[str, dict] = {}
    exact_primary_tokens = {k: 0 for k in TOKEN_KEYS}
    exact_primary_turns = 0.0
    exact_primary_energy = ZERO

    def stat_for(model: str) -> dict:
        return stats.setdefault(
            model,
            {
                "tokens": {k: 0 for k in TOKEN_KEYS},
                "allocated_turns": 0.0,
                "compactions": 0,
                "seconds": ZERO,
                "energy_kwh": ZERO,
                "carbon_gco2e": ZERO,
            },
        )

    ledger_path = ROOT / ".llm_resource_tally/ledger/ledger.jsonl"
    with ledger_path.open(encoding="utf-8") as f:
        for row_index, line in enumerate(f, 1):
            if not line.strip():
                continue
            row = json.loads(line)
            repo = str(row.get("r") or "")
            if repo not in LEDGER_REPOSITORIES:
                continue
            recorded = parse_dt(row.get("rec"))
            if recorded is not None and recorded > cutoff_dt:
                continue
            commit = str(row.get("c") or "")
            if repo == PRIMARY_REPOSITORY and commit in excluded_sha:
                continue
            is_exact_primary = repo == PRIMARY_REPOSITORY and commit in exact_primary_shas

            if row.get("k") == "cx":
                model = canonical_model_name(str((row.get("m") or ["<unknown>"])[0]))
                peak, summary_chars = (list(row.get("cp") or [0, 0]) + [0, 0])[:2]
                output = Interval.exact(float(summary_chars)) / Interval.coerce(stack_cfg["summary_chars_per_token"])
                _seconds, energy, carbon = serving_metrics(
                    {"input": int(peak or 0), "cache_write": 0, "cache_read": 0, "output": 0},
                    1.0,
                    stack,
                    output=output,
                )
                stat = stat_for(model)
                stat["compactions"] += 1
                add_metric(stat, "seconds", _seconds)
                add_metric(stat, "energy_kwh", energy)
                add_metric(stat, "carbon_gco2e", carbon)
                if is_exact_primary:
                    exact_primary_energy += energy
                continue

            if "t" not in row:
                continue
            row_tokens = token_dict(row.get("t"))
            by_model_raw = row.get("bm") or {}
            if by_model_raw:
                by_model = {canonical_model_name(str(m)): token_dict(v) for m, v in by_model_raw.items()}
            else:
                model = canonical_model_name(str((row.get("m") or ["<unknown>"])[0]))
                by_model = {model: row_tokens}

            for kind in TOKEN_KEYS:
                observed = sum(tokens[kind] for tokens in by_model.values())
                if observed != row_tokens[kind]:
                    raise ValueError(
                        f"ledger row {row_index}: by-model {kind} sum {observed} != row total {row_tokens[kind]}"
                    )

            weights = {model: sum(tokens.values()) for model, tokens in by_model.items()}
            total_weight = sum(weights.values())
            row_turns = float(row.get("n") or 0)
            for model, tokens in by_model.items():
                share = weights[model] / total_weight if total_weight else 1.0 / max(1, len(by_model))
                turns = row_turns * share
                seconds, energy, carbon = serving_metrics(tokens, turns, stack)
                stat = stat_for(model)
                stat["allocated_turns"] += turns
                for kind in TOKEN_KEYS:
                    stat["tokens"][kind] += tokens[kind]
                add_metric(stat, "seconds", seconds)
                add_metric(stat, "energy_kwh", energy)
                add_metric(stat, "carbon_gco2e", carbon)
                if is_exact_primary:
                    exact_primary_turns += turns
                    for kind in TOKEN_KEYS:
                        exact_primary_tokens[kind] += tokens[kind]
                    exact_primary_energy += energy

    prices = load_prices()
    rows = []
    total_tokens = {k: 0 for k in TOKEN_KEYS}
    total_cost = 0.0
    total_cost_complete = True
    total_energy = ZERO
    total_carbon = ZERO

    for model, stat in stats.items():
        tokens = stat["tokens"]
        if model == "<synthetic>" and sum(tokens.values()) == 0:
            continue
        cost = price_row(tokens, prices.get(model, {}))
        if cost is None:
            total_cost_complete = False
        else:
            total_cost += cost
        for kind in TOKEN_KEYS:
            total_tokens[kind] += tokens[kind]
        total_energy += stat["energy_kwh"]
        total_carbon += stat["carbon_gco2e"]
        rows.append(
            {
                "model": model,
                **{f"{k}_tokens": tokens[k] for k in TOKEN_KEYS},
                "billable_input_tokens": tokens["input"] + tokens["cache_write"] + tokens["cache_read"],
                "allocated_turns": stat["allocated_turns"],
                "compactions": stat["compactions"],
                "api_equivalent_usd": "" if cost is None else f"{cost:.6f}",
                "energy_kwh_low": stat["energy_kwh"].low,
                "energy_kwh_central": stat["energy_kwh"].central,
                "energy_kwh_high": stat["energy_kwh"].high,
                "carbon_kgco2e_low": stat["carbon_gco2e"].low / 1000.0,
                "carbon_kgco2e_central": stat["carbon_gco2e"].central / 1000.0,
                "carbon_kgco2e_high": stat["carbon_gco2e"].high / 1000.0,
            }
        )

    rows.sort(key=lambda r: r["energy_kwh_central"], reverse=True)

    # Billing sensitivity: all Anthropic cache writes are 1h rather than 5m.
    one_hour_total = total_cost if total_cost_complete else None
    if one_hour_total is not None:
        mult = float(assumptions["pricing_sensitivity"]["anthropic_cache_write"]["one_hour_multiplier_of_base_input"])
        for row in rows:
            if not row["model"].startswith("claude-"):
                continue
            price = prices[row["model"]]
            base = float(price["input_usd_per_million"])
            five_min = float(price["cache_write_usd_per_million"])
            one_hour_total += row["cache_write_tokens"] * (base * mult - five_min) * 1e-6

    cross = assumptions["cross_check_per_token"]
    billable_input = total_tokens["input"] + total_tokens["cache_write"] + total_tokens["cache_read"]
    cross_wh = total_tokens["output"] * float(cross["wh_per_output_token"]) + billable_input * float(cross["wh_per_input_token"])
    cross_energy = cross_wh * float(cross["pue"]) * 0.001
    cross_carbon_kg = cross_energy * float(cross["grid_gco2e_per_kwh"]) / 1000.0

    expected_exact = accounting_summary["exact_on_history"]
    exact_billable_input = (
        exact_primary_tokens["input"]
        + exact_primary_tokens["cache_write"]
        + exact_primary_tokens["cache_read"]
    )
    if exact_billable_input != int(expected_exact["billable_input_tokens"]):
        raise ValueError("resource valuation exact-primary billable-input total disagrees with accounting summary")
    if exact_primary_tokens["output"] != int(expected_exact["output_tokens"]):
        raise ValueError("resource valuation exact-primary output total disagrees with accounting summary")

    commit_share = float(coverage["exact_commit_share"])
    raw_lean_churn_share = float(coverage["exact_lean_line_churn_share"])
    adjusted_lean_churn_share = float(coverage["adjusted_exact_lean_line_churn_share"])
    if not (
        0 < commit_share <= 1
        and 0 < raw_lean_churn_share <= 1
        and 0 < adjusted_lean_churn_share <= 1
    ):
        raise ValueError("coverage shares must lie in (0, 1]")
    extrapolation = {
        "commit_scaled": {
            "billable_input_tokens": exact_billable_input / commit_share,
            "output_tokens": exact_primary_tokens["output"] / commit_share,
            "energy_kwh_central": exact_primary_energy.central / commit_share,
        },
        "raw_lean_churn_scaled": {
            "billable_input_tokens": exact_billable_input / raw_lean_churn_share,
            "output_tokens": exact_primary_tokens["output"] / raw_lean_churn_share,
            "energy_kwh_central": exact_primary_energy.central / raw_lean_churn_share,
        },
        "adjusted_lean_churn_scaled": {
            "billable_input_tokens": exact_billable_input / adjusted_lean_churn_share,
            "output_tokens": exact_primary_tokens["output"] / adjusted_lean_churn_share,
            "energy_kwh_central": exact_primary_energy.central / adjusted_lean_churn_share,
        },
    }

    assumptions_sha = hashlib.sha256(ASSUMPTIONS_PATH.read_bytes()).hexdigest()
    out = {
        "schema": "formalization-draft2/resource-valuation-output/v1",
        "through_commit": CUTOFF,
        "assumptions_version": assumptions["version"],
        "assumptions_sha256": assumptions_sha,
        "pricing_file": PRICING_PATH.name,
        "scope": assumptions["scope"],
        "rows": rows,
        "totals": {
            **{f"{k}_tokens": total_tokens[k] for k in TOKEN_KEYS},
            "billable_input_tokens": billable_input,
            "api_equivalent_usd": total_cost if total_cost_complete else None,
            "api_equivalent_usd_all_anthropic_1h_cache": one_hour_total,
            "energy_kwh": {
                "low": total_energy.low,
                "central": total_energy.central,
                "high": total_energy.high,
            },
            "carbon_kgco2e": {
                "low": total_carbon.low / 1000.0,
                "central": total_carbon.central / 1000.0,
                "high": total_carbon.high / 1000.0,
            },
            "per_token_cross_check": {
                "energy_kwh": cross_energy,
                "carbon_kgco2e": cross_carbon_kg,
            },
            "exact_primary_subset": {
                **{f"{k}_tokens": exact_primary_tokens[k] for k in TOKEN_KEYS},
                "billable_input_tokens": exact_billable_input,
                "turns": exact_primary_turns,
                "energy_kwh_central": exact_primary_energy.central,
            },
            "coverage_scaled_extrapolation": extrapolation,
        },
        "method": "measured ledger x versioned pricing/serving assumptions; scenario bounds are not confidence intervals",
    }
    (GENERATED / "resource_valuation_20260817.json").write_text(json.dumps(out, indent=2) + "\n")

    fieldnames = list(rows[0].keys()) if rows else ["model"]
    with (GENERATED / "resource_valuation_20260817.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)

    macros = [
        "% Generated by build_resource_valuation_20260817.py; do not edit by hand.",
        f"\\newcommand{{\\ResourceAssumptionsVersion}}{{{latex_escape(assumptions['version'])}}}",
        f"\\newcommand{{\\ResourceAssumptionsSHA}}{{{assumptions_sha}}}",
        f"\\newcommand{{\\MeasuredApiEquivalentCost}}{{\\${fmt_usd(total_cost)}}}" if total_cost_complete else "\\newcommand{\\MeasuredApiEquivalentCost}{unpriced}",
        f"\\newcommand{{\\MeasuredApiEquivalentCostOneHour}}{{\\${fmt_usd(one_hour_total)}}}" if one_hour_total is not None else "\\newcommand{\\MeasuredApiEquivalentCostOneHour}{unpriced}",
        f"\\newcommand{{\\ModeledOperationalEnergy}}{{{fmt_one(total_energy.central)}~kWh}}",
        f"\\newcommand{{\\PerTokenCrossCheckEnergy}}{{{fmt_one(cross_energy)}~kWh}}",
        f"\\newcommand{{\\ExactPrimaryOperationalEnergy}}{{{fmt_one(exact_primary_energy.central)}~kWh}}",
        f"\\newcommand{{\\CommitScaledOperationalEnergy}}{{{fmt_one(extrapolation['commit_scaled']['energy_kwh_central'])}~kWh}}",
        f"\\newcommand{{\\RawLeanChurnScaledOperationalEnergy}}{{{fmt_one(extrapolation['raw_lean_churn_scaled']['energy_kwh_central'])}~kWh}}",
        f"\\newcommand{{\\AdjustedLeanChurnScaledOperationalEnergy}}{{{fmt_one(extrapolation['adjusted_lean_churn_scaled']['energy_kwh_central'])}~kWh}}",
        f"\\newcommand{{\\CommitScaledBillableInputTokens}}{{{extrapolation['commit_scaled']['billable_input_tokens']:,.0f}}}",
        f"\\newcommand{{\\RawLeanChurnScaledBillableInputTokens}}{{{extrapolation['raw_lean_churn_scaled']['billable_input_tokens']:,.0f}}}",
        f"\\newcommand{{\\AdjustedLeanChurnScaledBillableInputTokens}}{{{extrapolation['adjusted_lean_churn_scaled']['billable_input_tokens']:,.0f}}}",
        f"\\newcommand{{\\CommitScaledOutputTokens}}{{{extrapolation['commit_scaled']['output_tokens']:,.0f}}}",
        f"\\newcommand{{\\RawLeanChurnScaledOutputTokens}}{{{extrapolation['raw_lean_churn_scaled']['output_tokens']:,.0f}}}",
        f"\\newcommand{{\\AdjustedLeanChurnScaledOutputTokens}}{{{extrapolation['adjusted_lean_churn_scaled']['output_tokens']:,.0f}}}",
        f"\\newcommand{{\\ResourceEnergyScenarioLow}}{{{fmt_one(total_energy.low)}~kWh}}",
        f"\\newcommand{{\\ResourceEnergyScenarioHigh}}{{{fmt_one(total_energy.high)}~kWh}}",
    ]
    (SNAPSHOTS / "resource_valuation_macros.tex").write_text("\n".join(macros) + "\n")

    summary_table = [
        "% Generated by build_resource_valuation_20260817.py; do not edit by hand.",
        r"\begin{tabular}{lrrr}",
        r"\toprule",
        r"Quantity & \shortstack{Observed\\lower bound} & \shortstack{Linear extrapolation\\commit coverage} & \shortstack{Linear extrapolation\\adjusted text coverage} \\",
        r"\midrule",
        fr"Billable input (B tokens) & {billable_input / 1e9:.2f} & {extrapolation['commit_scaled']['billable_input_tokens'] / 1e9:.2f} & {extrapolation['adjusted_lean_churn_scaled']['billable_input_tokens'] / 1e9:.2f} \\",
        fr"Output (M tokens) & {total_tokens['output'] / 1e6:.1f} & {extrapolation['commit_scaled']['output_tokens'] / 1e6:.1f} & {extrapolation['adjusted_lean_churn_scaled']['output_tokens'] / 1e6:.1f} \\",
        fr"Modeled operational energy (kWh) & {total_energy.central:,.0f} & {extrapolation['commit_scaled']['energy_kwh_central']:,.0f} & {extrapolation['adjusted_lean_churn_scaled']['energy_kwh_central']:,.0f} \\",
        r"\bottomrule",
        r"\end{tabular}",
    ]
    (SNAPSHOTS / "resource_coverage_extrapolation_table.tex").write_text("\n".join(summary_table) + "\n")

    table = [
        "% Generated by build_resource_valuation_20260817.py; do not edit by hand.",
        r"\begin{tabular}{lrrrr}",
        r"\toprule",
        r"Model & Lower-bound input & Lower-bound output & Lower-bound API-equiv. & Modeled energy \\",
        r" & (B tokens) & (M tokens) & (USD) & (kWh) \\",
        r"\midrule",
    ]
    for row in rows:
        cost = row["api_equivalent_usd"]
        cost_text = "--" if cost == "" else f"{float(cost):,.0f}"
        table.append(
            f"{latex_escape(row['model'])} & {row['billable_input_tokens'] / 1e9:.3f} & "
            f"{row['output_tokens'] / 1e6:.3f} & {cost_text} & "
            + fr"{row['energy_kwh_central']:.1f} \\")
    table += [
        r"\midrule",
        f"Total & {billable_input / 1e9:.3f} & {total_tokens['output'] / 1e6:.3f} & "
        + (f"{total_cost:,.0f}" if total_cost_complete else "--")
        + fr" & {total_energy.central:.1f} \\",
        r"\bottomrule",
        r"\end{tabular}",
    ]
    (SNAPSHOTS / "resource_valuation_table.tex").write_text("\n".join(table) + "\n")



if __name__ == "__main__":
    main()
