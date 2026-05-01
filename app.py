from flask import Flask, jsonify, request, render_template
from flask_cors import CORS
import random
import itertools
from collections import defaultdict

app = Flask(__name__, template_folder=".", static_folder=".")
CORS(app, origins="*", supports_credentials=True)

# ─────────────────────────────────────────────
#  Knowledge Base & Resolution Engine
# ─────────────────────────────────────────────

class Literal:
    def __init__(self, name, negated=False):
        self.name = name
        self.negated = negated

    def negate(self):
        return Literal(self.name, not self.negated)

    def __eq__(self, other):
        return self.name == other.name and self.negated == other.negated

    def __hash__(self):
        return hash((self.name, self.negated))

    def __repr__(self):
        return f"{'¬' if self.negated else ''}{self.name}"


class KnowledgeBase:
    def __init__(self):
        self.clauses = []   # list of frozensets of Literals
        self.raw_facts = [] # human-readable strings
        self._clause_set = set()  # fast membership check

    def tell(self, clause_literals, description=""):
        clause = frozenset(clause_literals)
        if clause not in self._clause_set:
            self._clause_set.add(clause)
            self.clauses.append(clause)
        if description:
            self.raw_facts.append(description)

    def tell_biconditional(self, left_lit, right_lits, description=""):
        """left ⟺ (r1 ∨ r2 ∨ …)  →  two implications in CNF"""
        # left → (r1 ∨ r2 ∨ …)  becomes  (¬left ∨ r1 ∨ r2 ∨ …)
        self.tell([left_lit.negate()] + list(right_lits), description)
        # (r1 ∨ r2 ∨ …) → left  becomes  (¬r1 ∨ left) ∧ (¬r2 ∨ left) ∧ …
        for r in right_lits:
            self.tell([r.negate(), left_lit])

    def resolve(self, c1, c2):
        """Return all resolvents of two clauses."""
        resolvents = []
        for lit in c1:
            neg = lit.negate()
            if neg in c2:
                resolvent = (c1 - {lit}) | (c2 - {neg})
                resolvents.append(frozenset(resolvent))
        return resolvents

    def resolution_refutation(self, query_lit):
        """
        Prove query_lit by refutation: add ¬query_lit and try to derive ⊥.
        Uses linear resolution: only pair new clauses against all existing ones.
        Returns (proved, steps) where steps is list of dicts.
        """
        negated_query = frozenset([query_lit.negate()])
        old_clauses = list(self.clauses)  # existing KB
        new_clauses = [negated_query]     # frontier: start with negated query
        seen = set(self.clauses)
        seen.add(negated_query)
        steps = []
        steps.append({
            "step": 0,
            "description": f"Negated query: {query_lit.negate()}",
            "clauses": []
        })

        max_iterations = 80
        iteration = 0

        while new_clauses and iteration < max_iterations:
            iteration += 1
            next_new = []
            for new_c in new_clauses:
                # Only pair each new clause against all old clauses
                for old_c in old_clauses:
                    for r in self.resolve(new_c, old_c):
                        if r not in seen:
                            seen.add(r)
                            steps.append({
                                "step": len(steps),
                                "description": f"Resolve with {set(old_c)}",
                                "result": str(set(r)) if r else "∅"
                            })
                            if len(r) == 0:
                                steps.append({
                                    "step": len(steps),
                                    "description": "⊥ Empty clause derived — CONTRADICTION found!",
                                    "result": "∅"
                                })
                                return True, steps
                            next_new.append(r)
            old_clauses.extend(new_clauses)
            new_clauses = next_new

        return False, steps


# ─────────────────────────────────────────────
#  Wumpus World
# ─────────────────────────────────────────────

class WumpusWorld:
    def __init__(self, rows=4, cols=4, num_pits=3):
        self.rows = rows
        self.cols = cols
        self.num_pits = num_pits
        self.agent_pos = (0, 0)
        self.agent_alive = True
        self.gold_collected = False
        self.score = 0
        self.moves = 0
        self.visited = set()
        self.percepts_log = []
        self.inference_log = []
        self.kb = KnowledgeBase()
        self.cell_states = {}  # 'safe','pit','wumpus','unknown'
        self._safe_cache = {}  # cache: pos -> (is_safe, steps)
        self._place_hazards()
        self._init_cell_states()
        self._enter_cell(self.agent_pos)

    def _place_hazards(self):
        all_cells = [(r, c) for r in range(self.rows) for c in range(self.cols)
                     if (r, c) != (0, 0)]
        random.shuffle(all_cells)
        self.pits = set(all_cells[:self.num_pits])
        self.wumpus = all_cells[self.num_pits] if len(all_cells) > self.num_pits else None
        # Gold somewhere not at start
        gold_candidates = [c for c in all_cells if c not in self.pits and c != self.wumpus]
        self.gold = random.choice(gold_candidates) if gold_candidates else (self.rows-1, self.cols-1)

    def _init_cell_states(self):
        for r in range(self.rows):
            for c in range(self.cols):
                self.cell_states[(r, c)] = 'unknown'
        self.cell_states[(0, 0)] = 'safe'

    def _neighbors(self, r, c):
        result = []
        for dr, dc in [(-1,0),(1,0),(0,-1),(0,1)]:
            nr, nc = r+dr, c+dc
            if 0 <= nr < self.rows and 0 <= nc < self.cols:
                result.append((nr, nc))
        return result

    def _enter_cell(self, pos):
        r, c = pos
        self.visited.add(pos)
        self.cell_states[pos] = 'safe'
        # Invalidate safe cache since KB changed
        self._safe_cache.clear()

        has_breeze = any(n in self.pits for n in self._neighbors(r, c))
        has_stench = self.wumpus and any(n == self.wumpus for n in self._neighbors(r, c))
        has_glitter = (pos == self.gold and not self.gold_collected)

        percepts = []
        if has_breeze: percepts.append('Breeze')
        if has_stench: percepts.append('Stench')
        if has_glitter: percepts.append('Glitter')

        self.percepts_log.append({
            "pos": pos,
            "percepts": percepts
        })

        # Update KB with biconditional rules
        cell_key = f"B_{r}_{c}" if has_breeze else f"NB_{r}_{c}"
        b_lit = Literal(f"B_{r}_{c}", negated=not has_breeze)
        s_lit = Literal(f"S_{r}_{c}", negated=not has_stench)

        neighbors = self._neighbors(r, c)

        # Breeze biconditional
        pit_lits = [Literal(f"P_{nr}_{nc}") for nr, nc in neighbors]
        if pit_lits:
            b_actual = Literal(f"B_{r}_{c}", negated=False)
            if has_breeze:
                self.kb.tell_biconditional(
                    b_actual, pit_lits,
                    f"B_{r}_{c} ⟺ {' ∨ '.join(str(p) for p in pit_lits)}"
                )
            else:
                # No breeze → no pits adjacent
                for pl in pit_lits:
                    self.kb.tell([pl.negate()], f"¬{pl} (no breeze at {r},{c})")

        # Stench biconditional
        w_lits = [Literal(f"W_{nr}_{nc}") for nr, nc in neighbors]
        if w_lits:
            s_actual = Literal(f"S_{r}_{c}", negated=False)
            if has_stench:
                self.kb.tell_biconditional(
                    s_actual, w_lits,
                    f"S_{r}_{c} ⟺ {' ∨ '.join(str(w) for w in w_lits)}"
                )
            else:
                for wl in w_lits:
                    self.kb.tell([wl.negate()], f"¬{wl} (no stench at {r},{c})")

        # Mark safe (visited)
        self.kb.tell([Literal(f"P_{r}_{c}", negated=True)], f"¬P_{r}_{c} (visited)")
        self.kb.tell([Literal(f"W_{r}_{c}", negated=True)], f"¬W_{r}_{c} (visited)")

        # Check hazard
        if pos in self.pits:
            self.agent_alive = False
            self.score -= 1000
            self.cell_states[pos] = 'pit'
        elif pos == self.wumpus:
            self.agent_alive = False
            self.score -= 1000
            self.cell_states[pos] = 'wumpus'

        return percepts

    def ask_safe(self, pos):
        """Use resolution refutation to prove a cell is safe. Results are cached."""
        if pos in self._safe_cache:
            return self._safe_cache[pos]
        r, c = pos
        # Fast-path: O(1) unit-clause check (covers most no-breeze/no-stench cells)
        no_pit_unit  = frozenset([Literal(f"P_{r}_{c}", negated=True)]) in self.kb._clause_set
        no_wump_unit = frozenset([Literal(f"W_{r}_{c}", negated=True)]) in self.kb._clause_set
        if no_pit_unit and no_wump_unit:
            fast = [{"step": 0, "description": f"Unit facts: safe cell (instant)", "result": "safe"}]
            self._safe_cache[pos] = (True, fast)
            return True, fast
        # Slow-path: full resolution refutation only when needed
        p_lit = Literal(f"P_{r}_{c}")
        w_lit = Literal(f"W_{r}_{c}")
        proved_no_pit,    pit_steps  = (True, []) if no_pit_unit  else self.kb.resolution_refutation(p_lit.negate())
        proved_no_wumpus, wump_steps = (True, []) if no_wump_unit else self.kb.resolution_refutation(w_lit.negate())
        steps = pit_steps + wump_steps
        safe  = proved_no_pit and proved_no_wumpus
        self._safe_cache[pos] = (safe, steps)
        return safe, steps

    def get_safe_moves(self):
        """Return list of (pos, is_safe, inference_steps) for adjacent unvisited cells."""
        r, c = self.agent_pos
        moves = []
        for neighbor in self._neighbors(r, c):
            if neighbor not in self.visited:
                is_safe, steps = self.ask_safe(neighbor)
                moves.append({
                    "pos": list(neighbor),
                    "safe": is_safe,
                    "inference_steps": len(steps),
                    "steps": steps[:10]  # limit for response size
                })
        return moves

    def move(self, target_pos):
        target_pos = tuple(target_pos)
        if not self.agent_alive:
            return {"error": "Agent is dead"}
        r, c = self.agent_pos
        if target_pos not in self._neighbors(r, c):
            return {"error": "Invalid move — not adjacent"}

        self.agent_pos = target_pos
        self.moves += 1
        self.score -= 1

        percepts = self._enter_cell(target_pos)

        result = {
            "pos": list(target_pos),
            "percepts": percepts,
            "alive": self.agent_alive,
            "score": self.score,
            "moves": self.moves,
            "gold_collected": self.gold_collected,
            "cell_states": {str(k): v for k, v in self.cell_states.items()},
            "visited": [list(p) for p in self.visited],
        }
        return result

    def grab_gold(self):
        if self.agent_pos == self.gold and not self.gold_collected:
            self.gold_collected = True
            self.score += 1000
            return True
        return False

    def get_state(self):
        safe_moves = self.get_safe_moves()
        return {
            "rows": self.rows,
            "cols": self.cols,
            "agent_pos": list(self.agent_pos),
            "alive": self.agent_alive,
            "score": self.score,
            "moves": self.moves,
            "gold": list(self.gold),
            "gold_collected": self.gold_collected,
            "visited": [list(p) for p in self.visited],
            "cell_states": {str(k): v for k, v in self.cell_states.items()},
            "percepts_log": self.percepts_log[-5:],
            "kb_facts": self.kb.raw_facts[-10:],
            "kb_clauses_count": len(self.kb.clauses),
            "safe_moves": safe_moves,
            "inference_total": sum(m["inference_steps"] for m in safe_moves),
        }

    def reveal(self):
        """Reveal ground truth for game over."""
        return {
            "pits": [list(p) for p in self.pits],
            "wumpus": list(self.wumpus) if self.wumpus else None,
            "gold": list(self.gold)
        }


# ─────────────────────────────────────────────
#  Global game store (single-session demo)
# ─────────────────────────────────────────────
games = {}


@app.route('/')
def home():
    return render_template('home.html')

@app.route('/game')
@app.route('/index.html')
def game():
    return render_template('index.html')


@app.route('/api/new_game', methods=['POST'])
def new_game():
    data = request.json or {}
    rows = max(3, min(8, int(data.get('rows', 4))))
    cols = max(3, min(8, int(data.get('cols', 4))))
    pits = max(1, min(rows * cols // 4, int(data.get('pits', 3))))
    game_id = data.get('game_id', 'default')
    games[game_id] = WumpusWorld(rows, cols, pits)
    return jsonify({"game_id": game_id, "state": games[game_id].get_state()})


@app.route('/api/state/<game_id>', methods=['GET'])
def get_state(game_id):
    if game_id not in games:
        return jsonify({"error": "Game not found"}), 404
    return jsonify(games[game_id].get_state())


@app.route('/api/move/<game_id>', methods=['POST'])
def move(game_id):
    if game_id not in games:
        return jsonify({"error": "Game not found"}), 404
    data = request.json
    result = games[game_id].move(data['pos'])
    state = games[game_id].get_state()
    return jsonify({**result, "state": state})


@app.route('/api/grab/<game_id>', methods=['POST'])
def grab(game_id):
    if game_id not in games:
        return jsonify({"error": "Game not found"}), 404
    grabbed = games[game_id].grab_gold()
    return jsonify({"grabbed": grabbed, "state": games[game_id].get_state()})


@app.route('/api/reveal/<game_id>', methods=['GET'])
def reveal(game_id):
    if game_id not in games:
        return jsonify({"error": "Game not found"}), 404
    return jsonify(games[game_id].reveal())


@app.route('/api/kb/<game_id>', methods=['GET'])
def get_kb(game_id):
    if game_id not in games:
        return jsonify({"error": "Game not found"}), 404
    g = games[game_id]
    clauses_display = []
    for c in g.kb.clauses[:50]:
        clauses_display.append(" ∨ ".join(str(l) for l in c))
    return jsonify({
        "clauses": clauses_display,
        "facts": g.kb.raw_facts,
        "total": len(g.kb.clauses)
    })


@app.route('/api/ask/<game_id>', methods=['POST'])
def ask(game_id):
    if game_id not in games:
        return jsonify({"error": "Game not found"}), 404
    data = request.json
    pos = tuple(data['pos'])
    g = games[game_id]
    safe, steps = g.ask_safe(pos)
    return jsonify({
        "pos": list(pos),
        "safe": safe,
        "steps": steps,
        "inference_steps": len(steps)
    })


if __name__ == '__main__':
    app.run(debug=True, port=5000)
