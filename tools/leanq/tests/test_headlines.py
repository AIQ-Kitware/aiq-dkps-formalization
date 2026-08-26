import json
import tempfile
import unittest
from pathlib import Path

from leanq.graph import environment_dependency_graph
from leanq.headlines import analyze_headlines, load_census_claims, prepare_project_explorer
from leanq.index import Decl


def decl(name, *, deps=(), module, library):
    return Decl(
        name=name,
        module=module,
        kind="theorem",
        is_prop=None,
        prop_valued=None,
        sorried=None,
        line=None,
        axioms=None,
        deps=tuple(deps),
        library=library,
        internal=False,
    )


def write_census(path, rows):
    path.write_text(json.dumps({"items": rows}), encoding="utf-8")


class HeadlineAnalysisTests(unittest.TestCase):
    def test_claim_group_consumption_and_nearest_integrations(self):
        rows = [
            decl("DK.unused", module="DavisKahan.Core", library="DavisKahan"),
            decl("DK.used", module="DavisKahan.Core", library="DavisKahan"),
            decl(
                "YWS.core",
                deps=("DK.used",),
                module="YuWangSamworth2015.Core",
                library="YuWangSamworth2015",
            ),
            decl(
                "Acharyya.bridge",
                deps=("YWS.core",),
                module="Acharyya2025.ConfigPerturbation",
                library="Acharyya2025",
            ),
            decl(
                "Quench.high",
                deps=("Acharyya.bridge",),
                module="DkpsQuench2026.Geometry",
                library="DkpsQuench2026",
            ),
            decl(
                "Quench.target",
                deps=("Quench.high",),
                module="DkpsQuench2026.QueryEfficiency",
                library="DkpsQuench2026",
            ),
            decl("Quench.other", module="DkpsQuench2026.Other", library="DkpsQuench2026"),
        ]
        semantic = environment_dependency_graph(rows).to_json()
        semantic["payloadKind"] = "semantic-index"
        semantic["libraries"] = ["DavisKahan", "YuWangSamworth2015", "Acharyya2025", "DkpsQuench2026"]

        with tempfile.TemporaryDirectory() as dpath:
            root = Path(dpath)
            dk = root / "davis-kahan-1970-full-source-census.json"
            yws = root / "yu-wang-samworth-2015-full-source-census.json"
            quench = root / "quench-2026-full-source-census.json"
            write_census(
                dk,
                [
                    {"id": "DK-H", "title": "Unused DK", "importance": "headline", "lean_declarations": ["DK.unused"]},
                    {"id": "DK-U", "title": "Used DK", "importance": "headline", "lean_declarations": ["DK.used"], "semantic_review": {"canonical_declarations": ["DK.used"], "supporting_declarations": []}},
                ],
            )
            write_census(yws, [{"id": "YWS-H", "title": "YWS population gap", "importance": "headline", "lean_declarations": ["YWS.core"], "semantic_review": {"canonical_declarations": ["YWS.core"], "supporting_declarations": []}}])
            write_census(
                quench,
                [
                    {"id": "Q-H", "title": "Quench headline", "importance": "headline", "lean_declarations": ["Quench.high"]},
                    {"id": "Q-U", "title": "Other Quench headline", "importance": "headline", "lean_declarations": ["Quench.other"]},
                ],
            )
            result = analyze_headlines(
                semantic,
                targets=["Quench.target"],
                census_paths=[dk, yws, quench],
                view="consumption",
            )

        claims = {row["id"]: row for row in result["headlineAnalysis"]["claims"]}
        self.assertFalse(claims["DK-H"]["consumed"])
        self.assertTrue(claims["DK-U"]["consumed"])
        self.assertEqual(claims["DK-U"]["nearestYWS"], "YWS.core")
        self.assertTrue(claims["YWS-H"]["consumed"])
        self.assertEqual(claims["YWS-H"]["representativeDeclaration"], "YWS.core")
        self.assertEqual(claims["YWS-H"]["nearestAcharyya"], "Acharyya.bridge")
        self.assertEqual(claims["YWS-H"]["nearestQuench"], "Quench.high")
        self.assertEqual(claims["YWS-H"]["nearestQuenchHeadline"]["id"], "Q-H")
        self.assertEqual(
            claims["YWS-H"]["witnessToTarget"],
            ["YWS.core", "Acharyya.bridge", "Quench.high", "Quench.target"],
        )
        self.assertTrue(claims["Q-H"]["consumed"])
        self.assertFalse(claims["Q-U"]["consumed"])
        self.assertEqual(claims["YWS-H"]["consumptionClass"], "canonical")
        self.assertEqual(
            result["headlineAnalysis"]["familyCounts"]["Yu–Wang–Samworth"],
            {"claims": 1, "consumed": 1, "canonical": 1, "supporting": 0},
        )
        edge_roles = {edge["role"] for edge in result["edges"]}
        self.assertIn("nearest-acharyya", edge_roles)
        self.assertIn("nearest-quench-headline", edge_roles)
        self.assertIn("headline-to-target", edge_roles)

    def test_only_requested_importance_is_loaded(self):
        with tempfile.TemporaryDirectory() as dpath:
            path = Path(dpath) / "quench-2026-full-source-census.json"
            write_census(
                path,
                [
                    {"id": "H", "title": "Headline", "importance": "headline", "lean_declarations": []},
                    {"id": "M", "title": "Major", "importance": "major", "lean_declarations": []},
                ],
            )
            rows = load_census_claims([path], importances=["headline"])
        self.assertEqual([row.id for row in rows], ["H"])

    def test_real_dependency_union_coverage_frontier_and_distances(self):
        rows = [
            decl("Base.shared", module="Foundation.Core", library="Foundation"),
            decl("A.a3", deps=("Base.shared",), module="A.Core", library="A"),
            decl("A.a2", deps=("A.a3",), module="A.Core", library="A"),
            decl("A.head", deps=("A.a2",), module="A.Main", library="A"),
            decl("B.b2", deps=("Base.shared",), module="B.Core", library="B"),
            decl("B.b1", deps=("B.b2",), module="B.Core", library="B"),
            decl("B.head", deps=("B.b1",), module="B.Main", library="B"),
            decl("C.private1", module="C.Core", library="C"),
            decl("C.private2", deps=("C.private1",), module="C.Core", library="C"),
            decl("C.head", deps=("C.private2",), module="C.Main", library="C"),
            decl("Unused.outside", module="Unused.Core", library="Unused"),
        ]
        semantic = environment_dependency_graph(rows).to_json()
        semantic["payloadKind"] = "semantic-index"
        with tempfile.TemporaryDirectory() as dpath:
            census = Path(dpath) / "example-full-source-census.json"
            write_census(census, [
                {"id": "A", "title": "Headline A", "importance": "headline", "lean_declarations": ["A.head"], "semantic_review": {"canonical_declarations": ["A.head"], "supporting_declarations": ["A.a2"]}},
                {"id": "B", "title": "Headline B", "importance": "headline", "lean_declarations": ["B.head"], "semantic_review": {"canonical_declarations": ["B.head"], "supporting_declarations": []}},
                {"id": "C", "title": "Headline C", "importance": "headline", "lean_declarations": ["C.head"], "semantic_review": {"canonical_declarations": ["C.head"], "supporting_declarations": []}},
            ])
            result = analyze_headlines(semantic, census_paths=[census])

        nodes = {row["id"]: row for row in result["nodes"]}
        self.assertEqual(result["payloadKind"], "headline-dependencies")
        self.assertNotIn("Unused.outside", nodes)
        self.assertEqual(set(nodes), {row.name for row in rows} - {"Unused.outside"})
        self.assertTrue(nodes["A.head"]["headline"])
        self.assertEqual(nodes["A.a2"]["headlineRole"], "supporting")
        self.assertEqual(nodes["Base.shared"]["headlineCoverageCount"], 2)
        self.assertTrue(nodes["Base.shared"]["sharedDependency"])
        self.assertTrue(nodes["Base.shared"]["sharedFrontier"])
        self.assertEqual(
            {(edge["source"], edge["target"]) for edge in result["edges"]},
            set(environment_dependency_graph(rows[:-1]).edges),
        )
        headline_rows = {row["declaration"]: row for row in result["headlineAnalysis"]["headlines"]}
        self.assertEqual(headline_rows["A.head"]["distanceToNearestSharedDependency"], 3)
        self.assertEqual(headline_rows["B.head"]["distanceToNearestSharedDependency"], 3)
        self.assertIsNone(headline_rows["C.head"]["nearestSharedDependency"])
        pair = next(row for row in result["headlineAnalysis"]["headlinePairs"] if row["headlines"] == ["A.head", "B.head"])
        self.assertEqual(pair["nearestSharedDependency"], "Base.shared")
        self.assertEqual(pair["distances"], [3, 3])
        structural = set(result["structuralNodeIds"])
        self.assertIn("A.head", structural)
        self.assertIn("B.head", structural)
        self.assertIn("Base.shared", structural)
        self.assertTrue(any(edge["collapsedNodeCount"] > 0 for edge in result["structuralEdges"]))

    def test_whole_project_keeps_supporting_landmark_outside_canonical_cone(self):
        rows = [
            decl("Pkg.base", module="Pkg.Core", library="Pkg"),
            decl("Pkg.head", deps=("Pkg.base",), module="Pkg.Main", library="Pkg"),
            decl("Pkg.alternative", module="Pkg.Alternative", library="Pkg"),
        ]
        semantic = environment_dependency_graph(rows).to_json()
        semantic["payloadKind"] = "semantic-index"
        with tempfile.TemporaryDirectory() as dpath:
            census = Path(dpath) / "pkg-census.json"
            write_census(census, [{
                "id": "H", "title": "Headline", "importance": "headline",
                "lean_declarations": ["Pkg.head", "Pkg.alternative"],
                "semantic_review": {
                    "canonical_declarations": ["Pkg.head"],
                    "supporting_declarations": ["Pkg.alternative"],
                },
            }])
            result = prepare_project_explorer(semantic, census_paths=[census])
        nodes = {row["id"]: row for row in result["nodes"]}
        self.assertTrue(nodes["Pkg.head"]["headline"])
        self.assertEqual(nodes["Pkg.alternative"]["headlineRole"], "supporting")
        self.assertTrue(nodes["Pkg.alternative"]["supportingClaims"])


if __name__ == "__main__":
    unittest.main()
