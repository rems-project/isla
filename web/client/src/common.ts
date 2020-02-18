import { Range, Locations } from './location'

export interface InteractiveRequest {
  lastId: number,
  state: string,
  active: number,
  tagDefs: string
}

export enum Arch {
  AArch64 = "aarch64",
  RISCV = "riscv"
}

function flags<T extends string>(o: Array<T>): {[K in T]: boolean} {
  return o.reduce((r, k) => { r[k] = false; return r }, Object.create(null));
}

export namespace Option {
  export const opts = flags([
    'show_integer_provenances',   // Show integer provenances when PVI
    'show_string_literals',       // Show string literals
    'show_pointer_bytes',         // Show all the bytes of a pointer value
    'hide_tau',                   // Hide tau transitions in execution graph
    'colour_all',                 // Colorise every expression
    'colour_cursor',              // Colorise expression on cursor
    'show_mem_order',             // Show memory graph in address order
    'align_allocs',               // Align allocations in a single column
  ])
  export type t = keyof typeof opts
  export const is = (s: string): s is t => Object.keys(opts).indexOf(s) !== -1
  export const Err = (opt: string) => new Error (`Expecting an 'option' type, got '${opt}'`)
}

export namespace CoreOpt {
  const opts = flags(['rewrite', 'sequentialise'])
  export type t = keyof typeof opts
  export const is = (s: string): s is t => Object.keys(opts).indexOf(s) !== -1
  export const Err = (opt: string) => new Error (`Expecting an 'core optimisation option' type, got '${opt}'`)
}

export namespace ExecOpt {
  const opts = flags(['libc'])
  export type t = keyof typeof opts
  export const is = (s: string): s is t => Object.keys(opts).indexOf(s) !== -1
  export const Err = (opt: string) => new Error (`Expecting an execution option, got '${opt}'`)
}

export namespace AllocModel {
  const opts = flags(['concrete', 'symbolic'])
  export type t = keyof typeof opts
  export const is = (s: string): s is t => Object.keys(opts).indexOf(s) !== -1
  export const Err = (opt: string) => new Error (`Expecting an 'allocation model' type, got '${opt}'`)
}

export namespace BmcModel {
  const opts = flags(['bmc_c11', 'bmc_rc11', 'bmc_rc11_hardcoded', 'bmc_linux', 'bmc_linux_no_rcu', 'bmc_custom'])
  export type t = keyof typeof opts
  export const is = (s: string): s is t => Object.keys(opts).indexOf(s) !== -1
  export const Err = (opt: string) => new Error (`Expecting an 'allocation model' type, got '${opt}'`)
}

export type Options = {[key in Option.t]: boolean}

export interface Model {
  alloc_model: AllocModel.t
  core_options: {[key in CoreOpt.t]: boolean}
  exec_options: {[key in ExecOpt.t]: boolean}
  switches: string []
}

export interface Interactive {
  tag_defs: string          // tag defs of current execution
  last_node_id: number      // seed to the server (last known node)
  current: Node             // current active step state
  next_options: number []   // next possible steps
  ranges: Range[]           // core expression positions
  counter: number           // step counter
  history: number []        // execution history
  arena: string             // current arena
  mem?: string              // DOT representation of memory
  exec?: string             // DOT representation of execution graph
}

export interface State {
  title: () => Readonly<string>
  litmus: () => Readonly<string>
  cat: () => Readonly<string>
  arch: Arch
  dirty: boolean
  locs: Locations[]
  console: string
  model: Model
  interactive?: Interactive
  options: Options,
  bmc_model: BmcModel.t,
  bmc_executions: string[],
}

export type ResultRequest =
  { status: 'execution', console: string, result: string} |
  { status: 'failure', console: string, result: string } |
  { status: 'bmc', result: string, executions: string[] } |
  { status: 'shorten', url: string }

export type Event =
  'update' |                // Update tab values
  'updateExecution' |       // Update execution result
  'mark' |                  // Mark location
  'markError' |             // Mark error location
  'clear' |                 // Clear all markings
  'highlight' |             // Highlight the entire file
  'dirty' |                 // Fired when file has changed
  'updateUI' |              // Update UI
  'updateArena' |           // Update arena
  'updateExecutionGraph' |  // Update execution graph
  'updateMemory' |          // Update memory graph (calls VIZ)
  'markInteractive' |       // Mark source locations when in interactive mode
  'layoutChanged' |         // GoldenLayout has been updated
  'updateBMC' |
  'updateCatFile'

export interface EventEmitter {
  on (eventName: 'clear', self: any, f: (locs: Locations) => void): void
  on (eventName: 'mark', self: any, f: (locs: Locations) => void): void
  on (eventName: 'markError', self: any, f: (line: number) => void): void
  on (eventName: 'dirty', self: any, f: () => void): void
  on (eventName: 'markInteractive', self: any, f: ((l:any, s: Readonly<State>) => void)): void
  on (eventName: Event, self: any, f: ((s: Readonly<State>) => void)): void
  off (self: any): void 
  once (f: ((s: Readonly<State>) => any)): any
  emit (eventName: 'clear'): void
  emit (eventName: 'mark'): void
  emit (eventName: Event, ...args: any[]): void
}