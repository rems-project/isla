import $ from 'jquery'
import _ from 'lodash'
import * as util from './util'
import View from './view'
import { State, Arch } from './common'
import { ModelGraph, Model } from './model'

interface Response {
  tag: string
  content?: Object
}

interface GraphResponse {
  graphs: ModelGraph[]
  objdump: string
  candidates: number
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

    // New limtus view
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

    // New cat view
    $('#new-cat').on('click', () => {
      let title = prompt('Please enter the file name', 'model.cat');
      if (title) {
        let litmus = this.getView().getLitmus();
        this.addView(litmus.getTitle(), litmus.getValue(), title, '', this.getView().getArch())
      }
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
    $('#select-arch-riscv').on('click', () => setArch(Arch.RISCV))

    $('#run').on('click', () => {
      this.request((response: Response) => {
        console.log(response)
        if (response.tag == 'Done') {
          let content = <GraphResponse>response.content
          let num_allowed = content.graphs.length
          this.getView().state.objdump = content.objdump
          if (num_allowed > 0) {
            console.log(content.graphs[0])
            let model = new Model(content.graphs)
            console.log(model.graphviz())
            this.getView().getGraph().setSVG(model.graphviz(), () => {})
            this.getView().state.console += "Allowed: " + num_allowed + " out of " + content.candidates + " allowed\n"
          } else {
            this.getView().state.console += "Forbidden: 0 out of " + content.candidates + " candidates allowed\n"
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

    this.updateUI = (s: State) => {
      $('#r-select-arch-aarch64').prop('checked', s.arch == Arch.AArch64)
      $('#r-select-arch-riscv').prop('checked', s.arch == Arch.RISCV)
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

  private getView(): Readonly<View> {
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
      timeout: 60000, /* 1 min timeout */
      data: {
        'arch': this.getView().getArch(),
        'cat': this.getView().getCat().getValue(),
        'litmus': this.getView().getLitmus().getValue(),
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
