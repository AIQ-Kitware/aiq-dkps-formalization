import io
import unittest
from argparse import Namespace
from pathlib import Path
from unittest.mock import Mock, call, patch

from leanq.cli import cmd_graph
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


class GraphCliScopeTests(unittest.TestCase):
    def test_graph_indexes_only_target_import_scope(self):
        project = Mock()
        project.root = Path("/tmp/demo")
        project.declaration_modules.return_value = ["App.Target"]
        project.libraries_for_import_closure.return_value = ["Foundation", "App"]
        rows = {
            "Foundation": [
                decl("Foundation.base", module="Foundation.Core", library="Foundation")
            ],
            "App": [
                decl(
                    "App.final",
                    deps=("Foundation.base",),
                    module="App.Target",
                    library="App",
                )
            ],
        }
        args = Namespace(
            project=None,
            presentation=None,
            target=["App.final"],
            root_module=None,
            include_lib=None,
            lib=None,
            exclude_lib=None,
            refresh=False,
            json=False,
            transitive_reduction=False,
            html=None,
            include_unresolved=False,
            headline=None,
            title=None,
            subtitle=None,
            out=None,
        )

        def scoped(_project, library, roots, **kwargs):
            self.assertIs(_project, project)
            self.assertEqual(roots, ["App.Target"])
            self.assertEqual(kwargs["detail"], "graph")
            return rows[library]

        with patch("leanq.cli.find_project", return_value=project), patch(
            "leanq.cli.ensure_scoped_index", side_effect=scoped
        ) as ensure, patch("sys.stdout", new_callable=io.StringIO) as stdout:
            status = cmd_graph(args)

        self.assertEqual(status, 0)
        self.assertEqual(ensure.call_count, 2)
        self.assertIn("libraries: Foundation, App", stdout.getvalue())
        project.libraries_for_import_closure.assert_called_once_with(["App.Target"])


if __name__ == "__main__":
    unittest.main()
