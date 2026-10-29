# EasySM Animation System

This is an Xcode-based SwiftUI-app for macOS.

## JSON Specifications

The animation engine is driven by two JSON files: an **automaton configuration** that defines the structure and layout of the state machine, and an **animation plan** that defines the sequence of steps to animate.

### Automaton Configuration

Defines the nodes (states), edges (transitions), and their visual layout. Decoded into the `AutomatonConfiguration` Swift type.

| Key | Type | Description |
|-----|------|-------------|
| `contractName` | string | Human-readable name of the contract being visualised. |
| `nodes` | array | List of state nodes (see below). |
| `edges` | array | List of directed edges between nodes (see below). |
| `designSize` | object | The design-space dimensions: `{ "width": number, "height": number }`. Used for scaling the view to fit. |
| `gridRows` | integer | Number of rows in the layout grid. |
| `gridColumns` | integer | Number of columns in the layout grid. |
| `nodeSize` | object | Size of each node view: `{ "width": number, "height": number }`. |

#### Node

| Key | Type | Description |
|-----|------|-------------|
| `id` | string | Unique identifier for the node. Also serves as the state key referenced by the animation plan. |
| `name` | string | Human-readable display name shown on the node. |
| `gridPosition` | object | Position on the layout grid: `{ "row": integer, "column": integer }` (zero-indexed). |

#### Edge

| Key | Type | Description |
|-----|------|-------------|
| `id` | string | Unique identifier for the edge. Referenced by `action` steps in the animation plan. |
| `label` | string | Static label displayed on the edge. |
| `source` | string | The `id` of the source node. |
| `target` | string | The `id` of the target node. |
| `bezier` | object | Cubic Bezier curve defining the edge path in design coordinates. Contains four points: `p0`, `c1`, `c2`, `p1`, each of the form `{ "x": number, "y": number }`. |
| `labelPosition` | object | Where to place the static label along the curve: `{ "t": number, "offset": { "width": number, "height": number } }`. `t` is a parameter in [0, 1] along the curve; `offset` is a pixel offset from that point. |

### Animation Plan

Defines the ordered sequence of steps that drive the animation. Decoded into the `AnimationPlan` Swift type.

| Key | Type | Description |
|-----|------|-------------|
| `initialState` | string | The `id` of the node that is active before any steps run. |
| `initialValue` | string or null | The value displayed on the initial state (e.g. `"∅"` or a tuple string). |
| `steps` | array | Ordered list of animation steps (see below). |

#### Step

Each step is an object with a `type` field that determines the remaining keys.

**State step** — transitions the active highlight to a node and displays a value:

| Key | Type | Description |
|-----|------|-------------|
| `type` | string | Must be `"state"`. |
| `node` | string | The `id` of the target node. |
| `valueText` | string or null | The value to display on the node. |

**Action step** — animates a token travelling along an edge:

| Key | Type | Description |
|-----|------|-------------|
| `type` | string | Must be `"action"`. |
| `edge` | string | The `id` of the edge to animate along. |
| `label` | string | Short label shown on the moving token. |
| `valueText` | string or null | Optional value shown beneath the token label. |

### Example Files

See the two example JSON files from the MultiSig example in the `Animation/Animation/` directory:

- `multisig-config.json` — automaton configuration for a two-state MultiSig contract (Holding, Collecting) with four edges (Propose, Pay, Cancel, Add key).
- `multisig-plan.json` — animation plan that walks through two full cycles: proposing, adding keys, paying, and cancelling.
