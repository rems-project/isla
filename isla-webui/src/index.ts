import $ from 'jquery'
import _ from 'lodash'
import './css/scheme.css'
import './css/goldenlayout-base.css'
import './css/goldenlayout-light-theme.css'
import './css/codemirror.css'
import './css/style.css'
import UI from './ui'

export function onLoad() {
    UI.addView('LB.litmus', '')
}

$(window).ready(onLoad)
