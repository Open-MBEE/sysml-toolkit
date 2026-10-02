"""Generation must reject ill-typed, missing and conflicting kind filters."""
import unittest
import derived_census as d


class Compositions(unittest.TestCase):
    def record(self, kind, rules=None):
        return dict(name="items", declaring=[dict(metaclass="Owner", type="Feature", multiplicity="0..*")], rules=rules or {"Owner": f"items = ownedFeature->selectByKind({kind})"})

    def test_type_validation(self):
        ancestors = {"Feature": set(), "PartUsage": {"Feature"}, "Package": set(), "Owner": set()}
        self.assertEqual(d.composition_rows([self.record("PartUsage")], ancestors)["items"][1], "PartUsage")
        for kind in ["Missing", "Package"]:
            with self.assertRaises(ValueError):
                d.composition_rows([self.record(kind)], ancestors)
        with self.assertRaises(ValueError):
            d.composition_rows([self.record("PartUsage", {"Owner": "items = ownedFeature->selectByKind(PartUsage)", "Other": "items = other->selectByKind(PartUsage)"})], ancestors)

    def test_normative_corrections(self):
        classes, props = {}, {}
        for source in d.SOURCES:
            classes.update(d.load(source, props))
        rows = d.composition_rows([dict(name=name, **record) for name, record in d.read_xmi().items()], d.ancestors(classes))
        for name in ["ownedFlow", "nestedFlow"]:
            self.assertEqual(rows[name][1], "FlowUsage")
        for name in ["ownedInterface", "nestedInterface"]:
            self.assertEqual(rows[name][1], "InterfaceUsage")


if __name__ == "__main__":
    unittest.main()
