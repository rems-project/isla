import $ from 'jquery'
import _ from 'lodash'
import * as util from './util'
import View from './view'
import { State } from './common'

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

    // Help
    $('#help').on('click', () => this.getView().newTab('Help'))

    // REMS
    $('#rems').on('click', () => {
      window.open('http://www.cl.cam.ac.uk/~pes20/rems/')
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
    view.getSource().refresh()
  }

  addView(title: string, source: string, config?: any) {
    let state = undefined
    if (this.currentView)
      state = _.cloneDeep(this.currentView.state)
    this.add(new View(title, source, state, config))
    this.refresh()
  }

  refresh() {
    // Refresh might happen without a view
    if (this.currentView)
      this.currentView.refresh()
  }

  public getDefaultHerdFile() {
    util.get('default.cat', (herd: string) => {
      const view = this.getView()
      if (!view.state.bmc_herd_file) {
        view.state.bmc_herd_file = herd
        view.emit('updateHerdFile')
      }
    }, () => {
      console.log('Error when trying to download "default.cat"... Using an empty file.')
    })
  }
}

const UI = new IslaUI()
export default UI

// This is used to debug, the singleton class UI is available in the web console
//@ts-ignore
window.UI = UI
