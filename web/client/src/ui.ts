import $ from 'jquery'
import _ from 'lodash'
import * as util from './util'
import View from './view'
import { State } from './common'

interface Response {
  tag: string
  content: Object
}

interface GraphResponse {
  graphs: string[]
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

    // Load File
    $('#load').on('click', () => {
      $('#file-input').trigger('click');
    })
    $('#file-input').on('change', (e) => {
      if (!(e.target instanceof HTMLInputElement) || !e.target.files) return
      let file = e.target.files[0]
      let reader = new FileReader()
      reader.onload = (e: ProgressEvent) => {
        if (e.target instanceof FileReader)
          this.addView(file.name, e.target.result as string, '', '', '')
      }
      reader.readAsText(file)
    })

    $('#run').on('click', () => {
      this.request((response: Response) => {
        console.log(response)
        if (response.tag == 'Done') {
          let content = <GraphResponse>response.content
          console.log(content.graphs[0])
          this.getView().getGraph().setSVG(content.graphs[0], () => {})
        }
      })
    })

    this.updateUI = (s: State) => {
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

  addView(title: string, litmus: string, catname: string, cat: string, isla_config: string, config?: any) {
    let state = undefined
    if (this.currentView)
      state = _.cloneDeep(this.currentView.state)
    this.add(new View(title, litmus, catname, cat, state, config))
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
        'arch': 'aarch64',
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
