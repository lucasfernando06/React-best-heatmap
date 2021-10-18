import React from 'react';
import { ThemeProvider } from 'styled-components';
import PropTypes from 'prop-types';
import { getDaysInYear } from 'date-fns'

import Heatmap from './components/Heatmap';

import './index.css';

const propsDefault = {
  showWeekDays: [1, 3, 5],
  startDate: new Date(),
  rangeDays: getDaysInYear(new Date()),
  values: [],
  showTooltip: true,
  showMonths: true,
  boxShape: 'square'
};

const Container = (props = {}) => {
  const options = Object.assign({}, propsDefault, props);

  return (
    <ThemeProvider theme={{}}>
      <Heatmap {...options} />
    </ThemeProvider>
  )
}

Container.propTypes = {
  showWeekDays: PropTypes.array,
  startDate: PropTypes.instanceOf(Date),
  values: PropTypes.array,
  showTooltip: PropTypes.bool,
  showMonths: PropTypes.bool,
  legend: PropTypes.array,
  locale: PropTypes.string,
  boxShape: PropTypes.string,
  contentBeforeLegend: PropTypes.string,
  contentAfterLegend: PropTypes.string,
}

export default Container;