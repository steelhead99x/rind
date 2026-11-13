"""pin.py's placing of pyrind versions against a requirement."""

import unittest

from pin import place


class PinTest(unittest.TestCase):
    def test_place(self):
        for version, want in [
            ("0.1.2", "below"),
            ("0.1.3", "within"),
            ("0.1.10", "within"),
            ("0.2.0", "past"),
        ]:
            with self.subTest(version=version):
                self.assertEqual(place(version, "pyrind>=0.1.3,<0.2"), want)

    def test_other_bounds_refused(self):
        for requirement in ["pyrind~=0.1.3", "pyrind>=0.1.3,!=0.1.4", "pyrind===0.1.3", "pyrind>0.1.2"]:
            with self.subTest(requirement=requirement), self.assertRaises(ValueError):
                place("0.1.3", requirement)


if __name__ == "__main__":
    unittest.main()
