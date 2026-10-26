"""Independent oracle: enumerate positional strategies, then detect reachable cycles.

This deliberately does not compute the solver's attractor fixed point.
Only used for finite regression evidence, not as a formal proof.
"""
from itertools import product


def validate_game(g):
    if type(g) is not dict or set(g) != {'n', 'owner', 'edges', 'goals'}:
        raise ValueError('invalid_input')
    n = g['n']
    if type(n) is not int or n < 0:
        raise ValueError('invalid_input')
    if type(g['owner']) is not list or len(g['owner']) != n or any(type(x) is not bool for x in g['owner']):
        raise ValueError('invalid_input')
    if type(g['edges']) is not list or len(g['edges']) != n:
        raise ValueError('invalid_input')
    def indices(xs):
        return type(xs) is list and all(type(x) is int and 0 <= x < n for x in xs) and len(xs) == len(set(xs))
    if not indices(g['goals']) or any(not indices(xs) or not xs for xs in g['edges']):
        raise ValueError('invalid_input')
    return g


def oracle(g):
    validate_game(g)
    n, edges, owner, goals = g['n'], g['edges'], g['owner'], set(g['goals'])
    controlled = [s for s in range(n) if owner[s]]
    won = [False] * n
    for choices in product(*(edges[s] for s in controlled)):
        selected = dict(zip(controlled, choices))
        graph = [[selected[s]] if owner[s] else edges[s] for s in range(n)]
        def can_avoid(start):
            active, finished = set(), set()
            def visit(s):
                if s in goals:
                    return False
                if s in active:
                    return True
                if s in finished:
                    return False
                active.add(s)
                if any(visit(t) for t in graph[s]):
                    return True
                active.remove(s)
                finished.add(s)
                return False
            return visit(start)
        for s in range(n):
            won[s] = won[s] or not can_avoid(s)
        if all(won):
            break
    return won


def games_up_to(upper=3):
    yield {'n': 0, 'owner': [], 'edges': [], 'goals': []}
    for n in range(1, upper + 1):
        subsets = [[i for i in range(n) if mask >> i & 1] for mask in range(1, 1 << n)]
        for rows in product(subsets, repeat=n):
            for owners in product((False, True), repeat=n):
                for mask in range(1 << n):
                    yield {'n': n, 'owner': list(owners), 'edges': [list(row) for row in rows],
                           'goals': [i for i in range(n) if mask >> i & 1]}


def check_certificate(g, r):
    validate_game(g)
    n = g['n']
    assert type(r) is dict and set(r) == {'winning', 'rank', 'agent_move', 'environment_move'}, 'output keys'
    for key in r:
        assert type(r[key]) is list and len(r[key]) == n, key
    w, rank, a, e = (r[k] for k in ('winning', 'rank', 'agent_move', 'environment_move'))
    assert all(type(x) is bool for x in w), 'winning types'
    assert all(type(x) is int and x >= 0 for x in rank), 'rank types'
    assert all(type(x) is int and 0 <= x < n for x in a + e), 'move range'
    goals = set(g['goals'])
    for s in range(n):
        edges = g['edges'][s]
        assert (a[s] if g['owner'][s] else e[s]) in edges, ('illegal strategy', s)
        if s in goals:
            assert w[s] and rank[s] == 0, ('goal', s)
        if w[s]:
            assert rank[s] <= n, ('rank bound', s)
            if s not in goals:
                successors = [a[s]] if g['owner'][s] else edges
                assert all(w[t] and rank[t] < rank[s] for t in successors), ('descent', s)
        else:
            assert s not in goals, ('losing goal', s)
            successors = edges if g['owner'][s] else [e[s]]
            assert all(not w[t] for t in successors), ('escape', s)
    return r
