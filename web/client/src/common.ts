import { Locations } from './location'

export enum Arch {
  AArch64 = "aarch64",
  AArch64VMSA = "aarch64-vmsa",
  RISCV32 = "riscv32",
  RISCV64 = "riscv64"
}

function flags<T extends string>(o: Array<T>): {[K in T]: boolean} {
  return o.reduce((r, k) => { r[k] = false; return r }, Object.create(null));
}

export namespace Option {
  export const opts = flags([
    'ignore_ifetch',             // Ignore instruction fetch events
    'hide_initial_irf',          // Hide irf edges from the initial state
    'exhaustive',                // Exhaustively enumerate all rf edges
    'armv8_page_tables',         // Setup and use ARMv8 page tables
    'remove_uninteresting',      // Remove 'uninteresting' translate events
    'merge_translations',        // Merge translate events from walks into a single event
    'merge_split_stages',        // Merge stages in walks into single events
  ])
  export type t = keyof typeof opts
  export const is = (s: string): s is t => Object.keys(opts).indexOf(s) !== -1
  export const Err = (opt: string) => new Error (`Expecting an 'option' type, got '${opt}'`)
}

export type Options = {[key in Option.t]: boolean}

export interface State {
  title: () => Readonly<string>
  litmus: () => Readonly<string>
  cat: () => Readonly<string>
  arch: Arch
  objdump: string
  dirty: boolean
  locs: Locations[]
  console: string
  options: Options,
}

export type Event =
  'update' |                // Update tab values
  'mark' |                  // Mark location
  'markError' |             // Mark error location
  'clear' |                 // Clear all markings
  'highlight' |             // Highlight the entire file
  'dirty' |                 // Fired when file has changed
  'updateUI' |              // Update UI
  'updateMemory' |          // Update memory graph (calls VIZ)
  'markInteractive' |       // Mark source locations when in interactive mode
  'layoutChanged'           // GoldenLayout has been updated

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
