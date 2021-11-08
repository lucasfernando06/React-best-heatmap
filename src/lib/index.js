import React from 'react';
import { ThemeProvider } from 'styled-components';
import PropTypes from 'prop-types';
import { getDaysInYear } from 'date-fns'

import Heatmap from './components/Heatmap';

import './index.css';
import 'react-popper-tooltip/dist/styles.css';

const propsDefault = {
  showWeekDays: [1, 3, 5],
  startDate: new Date(),
  rangeDays: getDaysInYear(new Date()),
  values: [],
  legend: [
    {
      isInRange: (v) => v === 0,
      color: '#EBEDF0',
      label: '= 0'
    },
    {
      isInRange: (v) => v === 1,
      color: '#9BE9A8',
      label: '= 1'
    },
    {
      isInRange: (v) => v === 2,
      color: '#40C463',
      label: '= 2'
    },
    {
      isInRange: (v) => v === 3,
      color: '#30A14E',
      label: '= 3'
    },
    {
      isInRange: (v) => v >= 4,
      color: '#216E39',
      label: '>= 4'
    },
  ],
  showBlockTooltip: true,
  showLegendTooltip: true,
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
};

Container.propTypes = {
  startDate: PropTypes.instanceOf(Date).isRequired,
  values: PropTypes.array,
  showWeekDays: PropTypes.array,
  showBlockTooltip: PropTypes.bool,
  showLegendTooltip: PropTypes.bool,
  showMonths: PropTypes.bool,
  locale: PropTypes.string,
  rangeDays: PropTypes.number,
  boxShape: PropTypes.string,
  legend: PropTypes.arrayOf(PropTypes.shape({
    isInRange: PropTypes.func.isRequired, // Example: (value) => value > 3
    color: PropTypes.string.isRequired,
    label: PropTypes.string.isRequired,
  })),
  contentBeforeLegend: PropTypes.string,
  contentAfterLegend: PropTypes.string,
};

export default Container;