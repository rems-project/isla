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

import $ from 'jquery'
import _ from 'lodash'
import * as util from './util'
import View from './view'
import { Option, State, Arch } from './common'
import { Model, ModelGraph } from './model'
import Widget from './widget'

interface Response {
  tag: string
  content?: Object
}

interface GraphResponse {
  graphs: ModelGraph[]
  objdump: string
  candidates: number
  shows: string[]
}

interface ErrorResponse {
  message: string
}

export class IslaUI {
  /** List of existing views */
  private views: View[]
  /** Current displayed view */
  private currentView?: View
  /** Contains the div where views are located */
  private dom: JQuery<HTMLElement>
  private updateUI: (s: State) => void

  constructor() {
    this.views = []
    this.dom = $('#views')
    this.currentView = undefined
    window.onresize = () => this.refresh()

    // Help
    $('#help').on('click', () => this.getView().newTab('Help'))

    // REMS
    $('#rems').on('click', () => {
      window.open('http://www.cl.cam.ac.uk/~pes20/rems/')
    })

    // New litmus view
    $('#new-litmus').on('click', () => {
      let title = prompt('Please enter the file name', 'litmus.toml');
      if (title) {
        let cat = this.getView().getCat();
        this.addView(title, '', cat.getTitle(), cat.getValue(), this.getView().getArch())
      }
    })

    // Load litmus file
    $('#load-litmus').on('click', () => {
      $('#file-input-litmus').trigger('click');
    })
    $('#file-input-litmus').on('change', (e) => {
      if (!(e.target instanceof HTMLInputElement) || !e.target.files) return
      let file = e.target.files[0]
      let reader = new FileReader()
      reader.onload = (e: ProgressEvent) => {
        if (e.target instanceof FileReader) {
          const cat = this.getView().getCat();
          this.addView(file.name, e.target.result as string, cat.getTitle(), cat.getValue(), this.getView().getArch())
        }
      }
      reader.readAsText(file)
    })

    let basic_aarch64: Widget.AArch64 | undefined
    $('#load-aarch64').on('click', () => {
      if (basic_aarch64 === undefined)
        basic_aarch64 = new Widget.AArch64()
      else
        basic_aarch64.show()
    })

    let basic_riscv64: Widget.RISCV64 | undefined
    $('#load-riscv64').on('click', () => {
      if (basic_riscv64 === undefined)
        basic_riscv64 = new Widget.RISCV64()
      else
        basic_riscv64.show()
    })

    let esop2020: Widget.ESOP2020 | undefined
    $('#load-esop2020').on('click', () => {
      if (esop2020 === undefined)
        esop2020 = new Widget.ESOP2020()
      else
        esop2020.show()
    })

    let aarch64vmsa: Widget.AArch64VMSA | undefined
    $('#load-aarch64-vmsa').on('click', () => {
      if (aarch64vmsa === undefined)
        aarch64vmsa = new Widget.AArch64VMSA
      else
        aarch64vmsa.show()
    })

    // New cat view
    $('#new-cat').on('click', () => {
      let title = prompt('Please enter the file name', 'model.cat');
      if (title) {
        let litmus = this.getView().getLitmus();
        this.addView(litmus.getTitle(), litmus.getValue(), title, '', this.getView().getArch())
      }
    })

    // Load any of the builtin cats
    const cats = ['aarch64', 'aarch64-vmsa-strong', 'esop2020', 'riscv']
    cats.forEach(name => {
      $(`#${name}-cat`).on('click', () => {
        util.get(`${name}.cat`, (cat: string) => {
          let editor = this.getView().getCat()
          editor.setFileName(`${name}.cat`)
          editor.setSource(cat)
        })
      })
    })

    // Save a cat file
    $('#save-cat').on('click', () => {
      const blob = new Blob([this.getView().getCat().getSource()], { type: 'text/plain' })
      var anchor = document.createElement('a')
      anchor.download = this.getView().getCat().getFileName()
      anchor.href = window.URL.createObjectURL(blob)
      anchor.dataset.downloadurl = ['text/plain', anchor.download, anchor.href].join(':')
      anchor.click()
    })

    // Load cat file
    $('#load-cat').on('click', () => {
      $('#file-input-cat').trigger('click');
    })
    $('#file-input-cat').on('change', (e) => {
      if (!(e.target instanceof HTMLInputElement) || !e.target.files) return
      let file = e.target.files[0]
      let reader = new FileReader()
      reader.onload = (e: ProgressEvent) => {
        if (e.target instanceof FileReader) {
          const litmus = this.getView().getLitmus();
          this.addView(litmus.getTitle(), litmus.getValue(), file.name, e.target.result as string, this.getView().getArch())
        }
      }
      reader.readAsText(file)
    })

    // Architecture selection radiobox
    const setArch = (arch: Arch) => {
      const view = this.getView();
      view.setArch(arch)
      this.updateUI(view.state)
    }
    $('#select-arch-aarch64').on('click', () => setArch(Arch.AArch64))
    $('#select-arch-aarch64-vmsa').on('click', () => setArch(Arch.AArch64VMSA))
    $('#select-arch-riscv32').on('click', () => setArch(Arch.RISCV32))
    $('#select-arch-riscv64').on('click', () => setArch(Arch.RISCV64))

    $('#run').on('click', () => {
      this.request((response: Response) => {
        console.log(response)
        if (response.tag == 'Done') {
          let content = <GraphResponse>response.content
          let num_allowed = content.graphs.length
          this.getView().state.objdump = content.objdump
          if (num_allowed > 0) {
            console.log(content.graphs[0])
            let model = new Model(content.graphs, content.shows, this.getView().state.options)
            console.log(model.graphviz())
            this.getView().getGraph().setModel(model)
            this.getView().state.console += "Allowed: " + num_allowed + " satisfiable solutions out of " + content.candidates + " candidates\n"
          } else {
            this.getView().state.console += "Forbidden: 0 satisfiable solutions out of " + content.candidates + " candidates\n"
          }
          this.getView().emit('update')
        } else if (response.tag = 'Error') {
          if (response.content != undefined) {
            let content = <ErrorResponse>response.content
            this.getView().state.console += content.message
            this.getView().emit('update')
          }
        }
      })
    })

    // Share
    let update_share_link = () => {
      if (!this.currentView) return
      const location = window.location
      const url = `${location.protocol}//${location.hostname}:${location.port}/#`
                + this.currentView.getEncodedState()
      $('#sharelink').val(url)
    }
    $('#sharebtn').on('click', () => {
      $('#sharelink').select()
      document.execCommand('Copy')
    })
    $('#share').on('mouseover', update_share_link)

    // Options
    const toggle = (m:{[k:string]:boolean}, k:string) => {
      m[k] = !m[k]
      $('#cb_'+k).prop('checked', m[k])
    }

    $('.option').on('click', (e) => {
      const opt = e.currentTarget.id
      if (!Option.is(opt)) throw Option.Err(opt)
      toggle(this.getView().state.options, opt)
      if (e.target.classList.contains('update-graph')) {
        console.log('updating graph')
        this.getView().getGraph().updateMemGraph()
      }
    })

    const updateCheckBoxes = (ids: {[key: string]: boolean}) =>
      _.map(ids, (v, k) => {
        //$('#'+k).toggleClass('disabled', !isConc)
        $('#cb_'+k).prop('checked', v)
      })

    this.updateUI = (s: State) => {
      updateCheckBoxes(s.options)

      $('#r-select-arch-aarch64').prop('checked', s.arch == Arch.AArch64)
      $('#r-select-arch-aarch64-vmsa').prop('checked', s.arch == Arch.AArch64VMSA)
      $('#r-select-arch-riscv32').prop('checked', s.arch == Arch.RISCV32)
      $('#r-select-arch-riscv64').prop('checked', s.arch == Arch.RISCV64)
      $('#arch-menu-label').html("Sail architecture (<i>" + s.arch as string + "</i>)")

      /** Align dropdown menu (left or right) */
      $('.contain-subitems').on('mouseenter', (e) => {
        const item = $(e.currentTarget)
        const dropdown = $(e.currentTarget).find('.dropdown')
        const offset = item.offset()
        if (offset !== undefined) {
          const left = offset.left
          const width = dropdown.width()
          const winWidth = $(window).width()
          if (width !== undefined && winWidth !== undefined) {
            if (left + width > winWidth) {
              dropdown.addClass('dropdown-right')
              dropdown.removeClass('dropdown-left')
            } else {
              dropdown.addClass('dropdown-left')
              dropdown.removeClass('dropdown-right')
            }
          }
        }
      })

    }
  }

  getView(): Readonly<View> {
    if (this.currentView)
      return this.currentView
    throw new Error("Panic: no view")
  }

  private setCurrentView(view: View) {
    if (this.currentView)
      this.currentView.hide()
    $('#current-view-title').text(view.title)
    this.currentView = view
    this.updateUI(view.state)
    view.show()
  }

  private add(view: View) {
    this.views.push(view)
    this.dom.append(view.dom)
    let nav = $('<div class="menu-item btn">' + view.title + '</div>')
    $('#dropdown-views').append(nav)
    nav.on('click', () => this.setCurrentView(view))
    view.on('updateUI', this, (s: State) => this.updateUI(s))
    this.setCurrentView(view)
    view.getLitmus().refresh()
    view.getCat().refresh()
  }

  addView(title: string, litmus: string, catname: string, cat: string, arch: Arch, config?: any) {
    let state = undefined
    if (this.currentView)
      state = _.cloneDeep(this.currentView.state)
    this.add(new View(title, litmus, catname, cat, state, config))
    this.getView().setArch(arch)
    this.updateUI(this.getView().state)
    this.refresh()
  }

  refresh() {
    // Refresh might happen without a view
    if (this.currentView)
      this.currentView.refresh()
  }

  /* Send an action request to the server */
  request(onSuccess: Function) {
    util.Cursor.wait()
    $.ajax({
      url: '/query',
      type: 'GET',
      headers: { Accept: 'application/json; charset=utf-8' },
      contentType: 'application/json; charset=utf-8',
      timeout: 240000, /* 4 min timeout */
      data: {
        'arch': this.getView().getArch(),
        'cat': this.getView().getCat().getValue(),
        'litmus': this.getView().getLitmus().getValue(),
        'litmus_format': this.getView().getLitmus().getFormat(),
        'ignore_ifetch': this.getView().state.options.ignore_ifetch,
        'exhaustive': this.getView().state.options.exhaustive,
        'armv8_page_tables': this.getView().state.options.armv8_page_tables,
        'remove_uninteresting': this.getView().state.options.remove_uninteresting,
        'merge_translations': this.getView().state.options.merge_translations,
        'merge_split_stages': this.getView().state.options.merge_split_stages,
      },
      dataType: 'json'
    }).done((data, status, query) => {
      onSuccess(data);
    }).fail((req, status) => {
      alert('Failed request! ' + status)
    }).always(() => {
      util.Cursor.done()
    })
  }
}

const UI = new IslaUI()
export default UI

// This is used to debug, the singleton class UI is available in the web console
//@ts-ignore
window.UI = UI
