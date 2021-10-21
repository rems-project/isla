// BSD 2-Clause License
//
// Copyright (c) 2020 Victor Gomes
// Copyright (c) 2020 Alasdair Armstrong
//
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:
// 
// 1. Redistributions of source code must retain the above copyright
// notice, this list of conditions and the following disclaimer.
// 
// 2. Redistributions in binary form must reproduce the above copyright
// notice, this list of conditions and the following disclaimer in the
// documentation and/or other materials provided with the distribution.
// 
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

import $ from "jquery"
import _ from "lodash"
import GoldenLayout from "golden-layout"
import Tabs from "./tabs"
import { triggerClick } from "./util"
import { State, Event, EventEmitter, Arch } from './common'

/** A view contains the state of a litmus test and cat model pair.
 * One can change a view in the dropdown in the top toolbar */
export default class View {
  title: string
  dom: JQuery<HTMLElement>

  public tabs: Tabs.Tab[]
  private litmus: Tabs.Litmus
  private cat: Tabs.Cat
  private layout!: GoldenLayout
  public state!: State

  /** Highlight has already been performed */
  private isHighlighted: boolean

  /** Source has been modified */
  private dirty: boolean

  /** Events */
  private events: { [eventName:string]: [any, Function][]; }

  /** Event emitter, the events are handled only for the current view */
  private ee: EventEmitter

  constructor (litmus_name: string, litmus: string, cat_name: string, cat: string, initial_state?: State, config?: GoldenLayout.Config) {
    this.tabs = []
    this.events = {}
    this.ee = {
      on: (e: Event, l: any, f: Function) => this.on(e, l, f),
      off: (f) => this.off(f),
      once: (f => f(this.state)),
      emit: (e: Event, ...args: any[]) => this.emit (e, ...args)
    }
    this.dirty = true
    this.on('dirty', this, () => {
      if (!this.dirty) {
        this.emit('clear')
        this.emit('updateMemory')
        this.emit('updateUI')
        this.dirty = true
      }
    })
    this.title  = litmus_name.split('.')[0] + " / " + cat_name.split('.')[0]
    this.isHighlighted = false
    if (initial_state)
      this.state = initial_state
    else
      this.setStateEmpty()

    this.litmus = new Tabs.Litmus(litmus_name, litmus, this.ee)
    this.tabs.push(this.litmus)

    this.cat = new Tabs.Cat(cat_name, cat, this.ee)
    this.tabs.push(this.cat)

    this.dom = $('<div class="view"></div>')
    $('#views').append(this.dom)
    this.initLayout(config)
  }

  private initLayout(config?: GoldenLayout.Config) {
    function component(title: string) {
      return {
        type: 'component',
        componentName: 'tab',
        componentState: { tab: title },
        title: title
      }
    }
    if (config == null) {
      config = {
        settings: {
          hasHeaders: true,
          constrainDragToContainer: true,
          reorderEnabled: true,
          selectionEnabled: false,
          popoutWholeStack: false,
          blockedPopoutsThrowError: true,
          closePopoutsOnUnload: true,
          showPopoutIcon: false,
          showMaximiseIcon: true,
          showCloseIcon: true
        },
        dimensions: {
          borderWidth: 5,
          minItemWidth: 150,
          headerHeight: 20,
          dragProxyWidth: 300,
          dragProxyHeight: 200
        },
        labels: {
          close: 'Close',
          maximise: 'Maximise',
          minimise: 'Minimise'
        },
        content: [{
          type: 'row',
          content: [{
            type: 'column',
            content: [{
              type: 'component',
              componentName: 'litmus',
              title: this.litmus.title,
              isClosable: false
            }, {
              type: 'stack',
              content: [
                component('Console'),
                component('Objdump')
             ]
            }
            ]
          }, {
            type: 'stack',
            content: [{
              type: 'component',
              componentName: 'cat',
              title: this.cat.title,
              isClosable: false
            }
            ]
          }, {
            type: 'stack',
            content: [
              component('EventGraph')
            ]
          }
          ]
        }]
      }
    }
    interface ContentItem extends GoldenLayout.ContentItem {
      componentName: string
      content: Tabs.Tab
    }
    let self = this // WARN: Golden Layout does not work with arrow function
    this.layout = new GoldenLayout (config, this.dom);
    this.layout.registerComponent('litmus', function (container: GoldenLayout.Container, state: any) {
      (container.parent as ContentItem).content = self.litmus
      container.getElement().append(self.litmus.dom)
      self.litmus.refresh()
    })
    this.layout.registerComponent('cat', function (container: GoldenLayout.Container, state: any) {
      (container.parent as ContentItem).content = self.cat
      container.getElement().append(self.cat.dom)
      self.cat.refresh()
    })
    this.layout.registerComponent('tab', function (container: GoldenLayout.Container, state: any) {
      const tab = Tabs.create(state.tab, self.ee, state.args)
      self.tabs.push(tab);
      (container.parent as ContentItem).content = tab
      container.getElement().append(tab.dom)
      container.setState(state)
      tab.initial(self.state)
      tab.refresh()
    })
    this.layout.on('itemDestroyed', (c: ContentItem) => {
      if (c.componentName == 'tab') {
        for (let i = 0; i < this.tabs.length; i++) {
          if (this.tabs[i] === c.content) {
            this.tabs.splice(i, 1)
            break
          }
        }
        this.off(c.content)
      }
    })
    this.layout.on( 'tabCreated', (header: GoldenLayout.Tab) => {
      if (header.contentItem.isComponent) {
        let tab = (header.contentItem as ContentItem).content
        header.element.on('mousedown', () => tab.refresh())
        tab.setActive = () => triggerClick(header.element[0])
        tab.close = () => header.contentItem.remove()
      }
    })
    this.layout.on('stateChanged', () => this.emit('layoutChanged'))
    this.layout.init()
  }

  private setStateEmpty() {
    this.state = {
      title: () => this.title,
      litmus: () => this.litmus.getValue(),
      cat: () => this.cat.getValue(),
      arch: Arch.AArch64,
      objdump: '',
      dirty: true,
      locs: [],
      console: '',
      options: {
        ignore_ifetch: true,
        hide_initial_irf: false,
        exhaustive: false,
        armv8_page_tables: false,
        remove_uninteresting: false,
        merge_translations: false,
        merge_split_stages: false,
      },
    }
  }

  setArch(arch: Arch) {
    this.state.arch = arch
  }

  getArch(): Arch {
    return this.state.arch
  }

  findTab(title: string) {
    for (let i = 0; i < this.tabs.length; i++) {
      if (Tabs.instanceOf(this.tabs[i], title)) {
        return this.tabs[i]
      }
    }
    return null
  }

  newTab(tab: string, title?: string, notClosable?: boolean, ...args: any []) {
    if (title === undefined) title = tab;
    this.layout.root.contentItems[0].addChild({
      type: 'component',
      componentName: 'tab',
      isClosable: !notClosable,
      title: title,
      componentState: { tab: tab, args: args }
    })
    this.refresh()
  }

  getEncodedState() {
    let miniConfig = GoldenLayout.minifyConfig(this.layout.toConfig())
    miniConfig.litmus_name = this.litmus.getFileName()
    miniConfig.litmus = this.litmus.getValue()
    miniConfig.cat_name = this.cat.getFileName()
    miniConfig.cat = this.cat.getValue()
    miniConfig.arch = this.getArch()
    return encodeURIComponent(JSON.stringify(miniConfig))
  }

  // Return this first instance (or create a new one)
  getTab(tab_name: string, title?: string, notClosable?: boolean) {
    let tab = this.findTab(tab_name)
    if (tab == null) {
      this.newTab(tab_name, title, notClosable)
      tab = <Tabs.Tab>this.findTab(tab_name)
    }
    return tab
  }

  getLitmus(): Readonly<Tabs.Litmus> {
    return this.litmus
  }

  getCat(): Readonly<Tabs.Cat> {
    return this.cat
  }

  getConsole() {
    return this.getTab('Console')
  }

  getGraph(): Readonly<Tabs.EventGraph> {
    return <Tabs.EventGraph>this.getTab('EventGraph')
  }

  show() {
    this.dom.show()
  }

  hide() {
    this.dom.hide()
  }

  refresh () {
    this.tabs.map((tab) => tab.refresh())
    this.layout.updateSize()
  }

  isDirty(): Readonly<boolean> {
    return this.dirty
  }

  on(e: Event, l: any, f: Function) {
    let listeners = this.events[e]
    if (!listeners) {
      listeners = []
      this.events[e] = listeners
    }
    listeners.push([l, f])
  }

  off(e_l: any) {
    if (typeof e_l === 'string') { // If an event name
      this.events[e_l] = []
    } else { // If a listener (unsubscribe all)
      for (const e in this.events) {
        this.events[e] = this.events[e].filter(listener => listener[0] !== e_l)
      }
    }
  }

  emit(e: string, ...args: any[]) {
    switch (e) {
      case 'highlight':
        if (this.isHighlighted || this.dirty) return
        this.isHighlighted = true
        break;
      case 'clear':
        this.isHighlighted = false
        break;
      case 'mark':
        break;
    }
    // DEBUG events
    console.log(e)
    const listeners = this.events[e]
    args.push(this.state)
    if (listeners)
      listeners.map(listener => listener[1].apply(listener[0], args))
  }

}
