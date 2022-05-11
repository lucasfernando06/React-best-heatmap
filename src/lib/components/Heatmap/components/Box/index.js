import React, { useState, memo } from "react";
import { format } from "date-fns";
import ReactTooltip from "react-tooltip";

import Container from "./components/Container";

const Box = ({ id, box, legend, locale, marginTop, boxShape, showTooltip }) => {
  const [canShowTooltip, setCanShowTooltip] = useState(false);

  const { date, value, valueLabel, color, onClick } = box;

  const getColor = () =>
    (legend && legend.find((l) => l.isInRange(value))?.color) || "#ebedf0";

  const label = valueLabel ? valueLabel : value;
  const finalColor = color ? color : getColor();

  const canClick = onClick != null && value != null;

  return (
    <>
      <Container
        id={id}
        data-for={id}
        data-tip
        onMouseEnter={() => setCanShowTooltip(true)}
        onMouseLeave={() => setCanShowTooltip(false)}
        onClick={() => canClick && onClick(date, value)}
        style={{
          marginTop,
          backgroundColor: finalColor,
          cursor: canClick ? "pointer" : "",
          borderRadius: boxShape === "circle" ? "50%" : "15%",
        }}
      />
      {canShowTooltip && (
        <ReactTooltip id={id} aria-haspopup="true">
          {showTooltip
            ? label
              ? label
              : date && locale
              ? `${format(date, "PP", { locale })} ${value ? `: ${value}` : ""}`
              : ""
            : null}
        </ReactTooltip>
      )}
    </>
  );
};

export default memo(Box);
