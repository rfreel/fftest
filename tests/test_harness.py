import copy
import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from oracle import oracle, games_up_to, check_certificate, validate_game


class HarnessTests(unittest.TestCase):
    def test_oracle_against_bounded_reachability(self):
        # A separate fixed-point calculation checks the strategy/cycle oracle.
        count = 0
        for g in games_up_to(3):
            winning = set(g['goals'])
            while True:
                following = winning | {s for s in range(g['n']) if
                    (any(t in winning for t in g['edges'][s]) if g['owner'][s]
                     else all(t in winning for t in g['edges'][s]))}
                if following == winning:
                    break
                winning = following
            self.assertEqual(oracle(g), [s in winning for s in range(g['n'])])
            count += 1
        self.assertEqual(count, 22101)

    def test_certificate_rejects_wrong_owner_quantifier_and_cycles(self):
        g = {'n': 2, 'owner': [False, True], 'edges': [[0, 1], [1]], 'goals': [1]}
        valid = {'winning': [False, True], 'rank': [0, 0], 'agent_move': [0, 1], 'environment_move': [0, 1]}
        check_certificate(g, valid)
        bad = copy.deepcopy(valid)
        bad['winning'][0], bad['rank'][0] = True, 1
        with self.assertRaises(AssertionError):
            check_certificate(g, bad)
        bad = copy.deepcopy(valid)
        bad['environment_move'][0] = 1
        with self.assertRaises(AssertionError):
            check_certificate(g, bad)

    def test_non_goal_agent_cycle_is_losing(self):
        g = {'n': 2, 'owner': [True, True], 'edges': [[0], [1]], 'goals': [1]}
        self.assertEqual(oracle(g), [False, True])

    def test_invalid_games(self):
        valid = {'n': 1, 'owner': [True], 'edges': [[0]], 'goals': []}
        for changes in ({'n': True}, {'edges': [[]]}, {'edges': [[0, 0]]},
                        {'edges': [[1]]}, {'goals': [True]}, {'owner': [1]}, {'extra': 1}):
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                validate_game(dict(valid, **changes))

    def test_game_count(self):
        self.assertEqual(sum(1 for _ in games_up_to(3)), 22101)


if __name__ == '__main__':
    unittest.main()
