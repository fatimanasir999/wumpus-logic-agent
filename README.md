# Wumpus Logic Agent — Web App

A fully interactive Wumpus World Knowledge-Based Agent with:
- **Propositional Logic Knowledge Base** (KB)
- **Resolution Refutation** (CNF-based contradiction proof)
- **Dynamic grid** (3×3 to 8×8)
- **Real-time inference metrics dashboard**
- **Biopunk dark UI** with amber × toxic-green theme & rich animations

## Stack
- **Backend**: Python 3 + Flask (Resolution engine, KB, Wumpus World simulation)
- **Frontend**: Vanilla JS + CSS animations (no frameworks)

## Run Locally

```bash
pip install -r requirements.txt
python app.py
```

Then open http://localhost:5000

## Keyboard Controls
- **W/A/S/D** or **Arrow Keys** — move agent
- **G** — grab gold
- Click any adjacent cell to move

## How It Works

### Knowledge Base
When the agent enters a cell, it `TELL`s the KB:
- `B_r_c ⟺ P_(r+1)_c ∨ P_(r-1)_c ∨ ...` (Breeze ↔ adjacent pit)
- `S_r_c ⟺ W_(r+1)_c ∨ ...` (Stench ↔ adjacent Wumpus)
- `¬P_r_c`, `¬W_r_c` (visited cells are safe)

### Resolution Refutation
Before moving to an unvisited cell `(r,c)`, the agent `ASK`s:
- Prove `¬P_r_c ∧ ¬W_r_c` by adding the negation and deriving ⊥ (empty clause)
- If a contradiction is found → cell is **provably safe**

### Scoring
- Move: −1 | Pit/Wumpus: −1000 | Gold: +1000
