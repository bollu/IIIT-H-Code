class FixSurveyUserRelation < ActiveRecord::Migration[5.0]
  def change
    drop_table :user_survey_answer_statuses
    add_reference :surveys, :user, foreign_key: true

  end
end
