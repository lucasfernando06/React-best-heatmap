import React from "react";

import Heatmap from "./components/Heatmap";

import "./index.css";

const defaultProps = {
  startDate: new Date(),
  values: [],
  showWeekDays: [1, 3, 5],
  showMonths: true,
  showBlockTooltip: true,
  showLegendTooltip: true,
  locale: "en",
  rangeDays: 365,
  boxShape: "square",
  legend: [
    {
      isInRange: (v) => v === 0,
      color: "#EBEDF0",
      label: "= 0",
    },
    {
      isInRange: (v) => v === 1,
      color: "#9BE9A8",
      label: "= 1",
    },
    {
      isInRange: (v) => v === 2,
      color: "#40C463",
      label: "= 2",
    },
    {
      isInRange: (v) => v === 3,
      color: "#30A14E",
      label: "= 3",
    },
    {
      isInRange: (v) => v >= 4,
      color: "#216E39",
      label: ">= 4",
    },
  ],
  contentBeforeLegend: "Less",
  contentAfterLegend: "More",
};

const Container = (props = {}) => {
  const options = Object.assign({}, defaultProps, props);

  return <Heatmap {...options} />;
};

export default Container;
